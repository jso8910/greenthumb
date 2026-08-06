#lang s-exp rosette

(require "../validator.rkt"
         "../inst.rkt"
         "../memory-racket.rkt"
         "../memory-rosette.rkt"
         "arm-machine.rkt")
(provide arm-validator%)

(define arm-validator%
  (class validator%
    (super-new)
    (inherit-field machine)
    (override get-constructor generate-input-states adjust-memory-config get-live-in)
    (define (get-constructor) arm-validator%)

    (define (load-width op-name)
      (cond
        [(member op-name '(ldrb-full# ldrsb-full#)) 1]
        [(member op-name '(ldrh-full# ldrsh-full#)) 2]
        [(equal? op-name 'ldr-full#) 4]
        [else #f]))

    (define (immediate-full-loads spec)
      (define loads '())
      (define supported? #t)
      (for ([my-inst (in-vector spec)])
        (define op-name
          (send machine get-base-opcode-name (vector-ref (inst-op my-inst) 0)))
        (define width (load-width op-name))
        (when width
          (define args (inst-args my-inst))
          (if (and (= (vector-length args) 6)
                   (number? (vector-ref args 0))
                   (number? (vector-ref args 1))
                   (number? (vector-ref args 2))
                   (number? (vector-ref args 3))
                   (number? (vector-ref args 4)))
              (set! loads
                    (cons (list width
                                (vector-ref args 0)
                                (vector-ref args 1)
                                (vector-ref args 2)
                                (vector-ref args 3)
                                (vector-ref args 4))
                          loads))
              (set! supported? #f))))
      (and supported? (not (empty? loads)) (reverse loads)))

    (define (full-load-address regs load)
      (match load
        [(list _width _rd rn raw-offset p u)
         (define base (vector-ref regs rn))
         (define offset (if (= u 1) raw-offset (- raw-offset)))
         (if (= p 1) (+ base offset) base)]))

    (define (byte-value state-index load-index byte-index)
      (modulo (+ 17 (* state-index 29) (* load-index 43) (* byte-index 71)) 256))

    (define (memory-inits-for-loads regs loads state-index)
      (define inits (make-hash))
      (for ([load loads]
            [load-index (in-naturals)])
        (define width (first load))
        (define address (full-load-address regs load))
        (for ([byte-index (in-range width)])
          (hash-set! inits
                     (+ address byte-index)
                     (byte-value state-index load-index byte-index))))
      inits)

    (define (seed-regs config loads state-index)
      (define regs
        (for/vector ([reg-id (in-range config)])
          (+ 3 (* state-index 11) reg-id)))
      (for ([load loads]
            [load-index (in-naturals)])
        (define rn (third load))
        (when (< rn config)
          (vector-set! regs rn (+ 64 (* state-index 128) (* load-index 32)))))
      regs)

    (define (load-backed-input-states n spec assumption)
      (and (not assumption)
           (let ([loads (immediate-full-loads spec)])
             (and loads
                  (let ([config (send machine get-config)])
                    (and (number? config)
                         (for/and ([load loads])
                           (< (third load) config))
                         (for/list ([state-index (in-range n)])
                           (define regs (seed-regs config loads state-index))
                           (define memory
                             (new memory-racket%
                                  [init (memory-inits-for-loads regs loads state-index)]))
                           (progstate regs memory (modulo state-index 16)))))))))

    (define (total-load-bytes loads)
      (for/sum ([load loads])
        (first load)))

    (define (adjust-memory-config encoded-code)
      (define loads (immediate-full-loads encoded-code))
      (if loads
          (begin
            (pretty-display "solver = load-backed concrete inputs")
            (init-memory-size)
            ;; Keep enough symbolic-memory slots for fallback validation paths
            ;; without asking the solver to discover the fixed load addresses.
            (let loop ([capacity 1])
              (when (<= capacity (total-load-bytes loads))
                (increase-memory-size)
                (loop (* 2 capacity))))
            (finalize-memory-size)
            (pretty-display "Finish adjusting memory config."))
          (super adjust-memory-config encoded-code)))

    (define (reg-operand-ids my-inst)
      (define args (inst-args my-inst))
      (define types (send machine get-arg-types (inst-op my-inst)))
      (for/list ([arg (in-vector args)]
                 [type types]
                 #:when (and (member type '(reg reg-sp))
                             (number? arg)))
        arg))

    (define (get-live-in code live-out)
      (if (immediate-full-loads code)
          (let* ([config (send machine get-config)]
                 [regs (make-vector config #f)])
            (for ([my-inst (in-vector code)])
              (for ([reg-id (reg-operand-ids my-inst)])
                (when (< reg-id config)
                  (vector-set! regs reg-id #t))))
            (progstate regs
                       #t
                       (progstate-n live-out)
                       (progstate-zf live-out)
                       (progstate-c live-out)
                       (progstate-v live-out)))
          (super get-live-in code live-out)))

    (define (generate-input-states n spec assumption #:db [db #f])
      (or (load-backed-input-states n spec assumption)
          (super generate-input-states n spec assumption #:db db)))

    ))
