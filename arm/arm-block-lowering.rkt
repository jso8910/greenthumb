#lang racket

(require "../inst.rkt")

(provide lower-block-transfers)

(define (string-op? value expected)
  (and (string? value) (equal? value expected)))

(define (numberish->number who value)
  (define parsed (cond
                   [(number? value) value]
                   [(string? value) (string->number value)]
                   [else #f]))
  (unless parsed
          (raise-user-error who "expected numeric instruction field, got ~a" value))
  parsed)

(define (reg-id value)
  (cond
    [(number? value) value]
    [(and (string? value)
          (> (string-length value) 1)
          (equal? (substring value 0 1) "r"))
     (string->number (substring value 1))]
    [else #f]))

(define (reg-name id)
  (format "r~a" id))

(define (mask-has-reg? mask id)
  (= (bitwise-bit-field mask id (add1 id)) 1))

(define (mask-regs mask)
  (for/list ([id (in-range 16)] #:when (mask-has-reg? mask id))
    id))

(define (live-reg? live-out id)
  (member id live-out))

(define (op-without-imm-marker op)
  (if (and (string? op)
           (> (string-length op) 0)
           (equal? (substring op (sub1 (string-length op))) "#"))
      (substring op 0 (sub1 (string-length op)))
      op))

(define (block-transfer-op op)
  (match (op-without-imm-marker op)
    ["ldm-full" 'load]
    ["stm-full" 'store]
    [_ #f]))

(define (block-transfer? my-inst)
  (and (inst-op my-inst)
       (vector? (inst-op my-inst))
       (> (vector-length (inst-op my-inst)) 0)
       (block-transfer-op (vector-ref (inst-op my-inst) 0))))

(define (pc-mentioned? my-inst)
  (and (inst-args my-inst)
       (for/or ([arg (in-vector (inst-args my-inst))])
         (or (equal? arg 15)
             (equal? arg "r15")
             (equal? arg "pc")))))

(define (any-pc-mentioned? insts)
  (for/or ([my-inst insts])
    (pc-mentioned? my-inst)))

(define (prior-popcount mask reg-id)
  (for/sum ([i (in-range reg-id)])
    (if (mask-has-reg? mask i) 1 0)))

(define (block-start-offset byte-count p u)
  (cond
    [(= u 1) (if (= p 1) 4 0)]
    [(= p 1) (- byte-count)]
    [else (+ (- byte-count) 4)]))

(define (offset->transfer-fields offset)
  (if (negative? offset)
      (values (number->string (- offset)) "0")
      (values (number->string offset) "1")))

(define (make-full-transfer load? cond rd rn offset)
  (define-values (abs-offset u) (offset->transfer-fields offset))
  (inst (vector (if load? "ldr-full" "str-full") cond "")
        (vector (reg-name rd) (reg-name rn) abs-offset "1" u "0")))

(define (make-writeback cond rn u byte-count)
  (inst (vector (if (= u 1) "add" "sub") cond "")
        (vector (reg-name rn) (reg-name rn) (number->string byte-count))))

(define (lower-block-transfer my-inst live-out)
  (define ops (inst-op my-inst))
  (define args (inst-args my-inst))
  (define kind (block-transfer-op (vector-ref ops 0)))
  (define load? (equal? kind 'load))
  (define cond (vector-ref ops 1))
  (define rn (reg-id (vector-ref args 0)))
  (define mask (numberish->number 'lower-block-transfers (vector-ref args 1)))
  (define p (numberish->number 'lower-block-transfers (vector-ref args 2)))
  (define u (numberish->number 'lower-block-transfers (vector-ref args 3)))
  (define w (numberish->number 'lower-block-transfers (vector-ref args 4)))
  (define regs (mask-regs mask))
  (define byte-count (* 4 (length regs)))

  (unless rn
          (raise-user-error 'lower-block-transfers
                            "unsupported block-transfer base register ~a"
                            (vector-ref args 0)))
  (when (zero? mask)
        (raise-user-error 'lower-block-transfers
                          "cannot lower empty block-transfer register list"))
  (when (mask-has-reg? mask rn)
        (raise-user-error
         'lower-block-transfers
         "cannot exactly lower block transfer with base register r~a in the register list"
         rn))
  (when (and load? (mask-has-reg? mask 15) (live-reg? live-out 15))
        (raise-user-error
         'lower-block-transfers
         "cannot optimize PC-writing block load when r15 is live-out"))
  (when (and (not load?) (mask-has-reg? mask 15) (> (prior-popcount mask 15) 0))
        (raise-user-error
         'lower-block-transfers
         "cannot exactly lower block store of r15 after earlier registers because it would change the PC-read instruction index"))

  (define start-offset (block-start-offset byte-count p u))
  (define transfers
    (for/list ([rd regs]
               #:unless (and load? (= rd 15) (not (live-reg? live-out 15))))
      (make-full-transfer load?
                          cond
                          rd
                          rn
                          (+ start-offset (* 4 (prior-popcount mask rd))))))
  (define writeback
    (if (= w 1)
        (list (make-writeback cond rn u byte-count))
        '()))
  (append transfers writeback))

(define (lower-block-transfers code live-out)
  (define insts (vector->list code))
  (define lowered
    (let loop ([remaining insts])
      (match remaining
        ['() '()]
        [(cons my-inst rest)
         (define replacement
           (if (block-transfer? my-inst)
               (lower-block-transfer my-inst live-out)
               (list my-inst)))
         (when (and (not (= (length replacement) 1))
                    (any-pc-mentioned? rest))
               (raise-user-error
                'lower-block-transfers
                "cannot lower block transfer before a later r15/pc operand because it would change GreenThumb's PC-read instruction index"))
         (append replacement (loop rest))])))
  (list->vector lowered))
