#lang racket

(require rackunit
         racket/file
         racket/list
         racket/runtime-path
         "../../inst.rkt"
         "../arm-parser.rkt"
         "../arm-machine.rkt"
         "../arm-printer.rkt"
         "../arm-stochastic.rkt")

(define-runtime-path arm-simulator-racket "../arm-simulator-racket.rkt")

(define machine (new arm-machine% [config 4]))
(define parser (new arm-parser%))
(define printer (new arm-printer% [machine machine]))
(define stochastic
  (new arm-stochastic%
       [machine machine]
       [printer printer]
       [validator #f]
       [simulator #f]
       [syn-mode #t]))

(define regs-live-none '#(#f #f #f #f))
(define memory-live-none #f)
(define flags-live (progstate regs-live-none memory-live-none #t))
(define flags-dead (progstate regs-live-none memory-live-none #f))
(define expected (progstate '#(0 0 0 0) #f #b1111))

(check-equal?
 (send stochastic correctness-cost expected (progstate '#(0 0 0 0) #f #b1111) flags-live)
 0)

(check-equal?
 (send stochastic correctness-cost expected (progstate '#(0 0 0 0) #f #b1110) flags-live)
 1)

(check-equal?
 (send stochastic correctness-cost expected (progstate '#(0 0 0 0) #f #b0000) flags-live)
 4)

(check-equal?
 (send stochastic correctness-cost expected (progstate '#(0 0 0 0) #f #b0000) flags-dead)
 0)

(define z-only-live (progstate regs-live-none memory-live-none #f #t #f #f))

(check-equal?
 (send stochastic correctness-cost expected (progstate '#(0 0 0 0) #f #b1011) z-only-live)
 1)

(define subs-inst
  (vector-ref
   (send printer encode (send parser ir-from-string "subs r0, r1, r2\n"))
   0))
(send machine reset-arg-ranges)
(define live-in-r1-r2 (progstate '#(#f #t #t #f) #f #t))
(define only-flags-live-out (progstate '#(#f #f #f #f) #f #t))
(define subs-ranges
  (send machine get-arg-ranges
        (inst-op subs-inst)
        subs-inst
        live-in-r1-r2
        #:live-out only-flags-live-out))

(check-equal? (vector->list (vector-ref subs-ranges 0)) '(0 1 2 3))
(check-equal? (vector->list (vector-ref subs-ranges 1)) '(1 2))
(check-equal? (vector->list (vector-ref subs-ranges 2)) '(1 2))

(define cmp-machine (new arm-machine% [config 4]))
(define cmp-printer (new arm-printer% [machine cmp-machine]))
(define cmp-code
  (send cmp-printer encode (send parser ir-from-string "cmp r1, r2\n")))
(define cmp-live-in (progstate '#(#f #t #t #f) #f #f #f #f #f))
(send cmp-machine reset-opcode-pool)
(send cmp-machine reset-arg-ranges)
(parameterize ([current-output-port (open-output-string)])
  (send cmp-machine analyze-args
        (vector)
        cmp-code
        (vector)
        cmp-live-in
        (progstate '#(#f #f #f #f) #f #f #t #f #f)))
(send cmp-machine analyze-opcode (vector) cmp-code (vector))

(define (base-opcode-name opcode-id)
  (vector-ref (send cmp-machine get-opcode-name opcode-id) 0))

(define cmp-pool
  (send cmp-machine get-valid-opcode-pool 0 1 cmp-live-in))

(check-true
 (for/or ([opcode-id cmp-pool])
   (equal? (base-opcode-name opcode-id) 'subs)))

(define (sorted-symbols xs)
  (sort (remove-duplicates xs) symbol<?))

(define (machine-base-opcode-names machine)
  (sorted-symbols (vector->list (vector-ref (get-field opcodes machine) 0))))

(define (simulator-base-opcode-names)
  (sorted-symbols
   (map (lambda (match)
          (string->symbol (substring match 1)))
        (regexp-match* #rx"`[a-z0-9#-]+"
                       (file->string arm-simulator-racket)))))

(define candidate-machine (new arm-machine% [config 5]))
(define candidate-printer (new arm-printer% [machine candidate-machine]))
(define candidate-stochastic
  (new arm-stochastic%
       [machine candidate-machine]
       [printer candidate-printer]
       [validator #f]
       [simulator #f]
       [syn-mode #t]))

(define machine-opcodes (machine-base-opcode-names candidate-machine))
(define simulator-opcodes (simulator-base-opcode-names))

(check-equal? (remove* machine-opcodes simulator-opcodes) '())
(check-equal? (remove* simulator-opcodes machine-opcodes) '())

(send candidate-machine reset-opcode-pool)
(send candidate-machine reset-arg-ranges)

(define all-live
  (progstate (make-vector 5 #t) #t #t #t #t #t))

(parameterize ([current-output-port (open-output-string)])
  (send candidate-machine analyze-args
        (vector)
        (vector)
        (vector)
        all-live
        all-live))
(send candidate-machine analyze-opcode (vector) (vector) (vector))

(define candidate-pool-names
  (sorted-symbols
   (map (lambda (opcode-id)
          (send candidate-machine get-base-opcode-name (vector-ref opcode-id 0)))
        (get-field opcode-pool candidate-machine))))

(check-equal? (remove* candidate-pool-names machine-opcodes)
              '(ldm-full# stm-full#))

(define stochastic-generation-failures
  (for/list ([opcode-id (get-field opcode-pool candidate-machine)]
             #:unless
             (with-handlers ([exn:fail? (lambda (e) #f)]
                             [string? (lambda (e) #f)])
               (send candidate-stochastic random-instruction
                     0 1 all-live opcode-id)))
    (send candidate-machine get-opcode-name opcode-id)))

(check-equal? stochastic-generation-failures '())
