#lang s-exp rosette

(require rackunit
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-simulator-racket.rkt"
         "../arm-simulator-rosette.rkt"
         "../arm-validator.rkt"
         "../../inst.rkt")

(current-bitwidth 32)

(define parser (new arm-parser%))

(define (encode printer asm)
  (send printer encode (send parser ir-from-string asm)))

(define (zero-init #:min [min #f] #:max [max #f] #:const [const #f]) 0)

(define (state-with-regs machine regs)
  (define base (send machine get-state zero-init))
  (progstate (vector-copy regs) (progstate-memory base) 0))

(define (make-regs sp)
  (define regs (make-vector 13 0))
  (vector-set! regs 0 #xab)
  (vector-set! regs 12 sp)
  regs)

(test-case
 "candidate stack scratch store is rejected without a stack policy"
 (define machine (new arm-machine% [config 13]))
 (define printer (new arm-printer% [machine machine]))
 (define simulator (new arm-simulator-racket% [machine machine]))
 (define input (state-with-regs machine (make-regs 100)))
 (define spec-out (send simulator interpret (encode printer "nop\n") input))
 (check-exn
  exn?
  (lambda ()
    (send simulator interpret
          (encode printer "strb r0, [r12, #-4]\n")
          input
          spec-out))))

(test-case
 "downward stack scratch allows offsets -1 through -size only"
 (define machine (new arm-machine% [config 13]))
 (send machine set-stack-scratch-config! 12 8 'downwards)
 (define printer (new arm-printer% [machine machine]))
 (define simulator (new arm-simulator-racket% [machine machine]))
 (define input (state-with-regs machine (make-regs 100)))
 (define spec-out (send simulator interpret (encode printer "nop\n") input))
 (define in-range-out
   (send simulator interpret
         (encode printer "strb r0, [r12, #-8]\n")
         input
         spec-out))
 (check-equal? (send (progstate-memory in-range-out) lookup-update 92) #xab)
 (check-exn
  exn?
  (lambda ()
    (send simulator interpret
          (encode printer "strb r0, [r12, #-9]\n")
          input
          spec-out)))
 (check-exn
  exn?
  (lambda ()
    (send simulator interpret
          (encode printer "strb r0, [r12, #0]\n")
          input
          spec-out))))

(test-case
 "upward stack scratch allows offsets +1 through +size only"
 (define machine (new arm-machine% [config 13]))
 (send machine set-stack-scratch-config! 12 8 'upwards)
 (define printer (new arm-printer% [machine machine]))
 (define simulator (new arm-simulator-racket% [machine machine]))
 (define input (state-with-regs machine (make-regs 100)))
 (define spec-out (send simulator interpret (encode printer "nop\n") input))
 (define in-range-out
   (send simulator interpret
         (encode printer "strb r0, [r12, #8]\n")
         input
         spec-out))
 (check-equal? (send (progstate-memory in-range-out) lookup-update 108) #xab)
 (check-exn
  exn?
  (lambda ()
    (send simulator interpret
          (encode printer "strb r0, [r12, #9]\n")
          input
          spec-out)))
 (check-exn
  exn?
  (lambda ()
    (send simulator interpret
          (encode printer "strb r0, [r12, #-1]\n")
          input
          spec-out))))

(test-case
 "ARM compression keeps and remaps a configured stack pointer"
 (define machine (new arm-machine%))
 (send machine set-stack-scratch-config! 12 32 'downwards)
 (define printer (new arm-printer% [machine machine]))
 (define-values (_compressed _live map-back _config)
   (send printer compress-state-space
         (send parser ir-from-string "add r0, r0, #1\n")
         '(0)))
 (define remapped (send machine remap-stack-scratch-config map-back))
 (check-equal? (vector-ref map-back (list-ref remapped 0)) 12)
 (check-equal? (list-ref remapped 1) 32)
 (check-equal? (list-ref remapped 2) 'downwards))

(test-case
 "ARM compression preserves r15 as the PC register"
 (define machine (new arm-machine%))
 (define printer (new arm-printer% [machine machine]))
 (define-values (compressed _live map-back config)
   (send printer compress-state-space
         (send parser ir-from-string
               "add r1, r1, r0
eor r4, r4, r5
add r2, r2, r15
add r3, r3, r0
eor r6, r6, r7
")
         '(2)))
 (check-true (> config 15))
 (check-equal? (vector-ref map-back 15) 15)
 (check-equal? (vector-ref (inst-args (vector-ref compressed 2)) 2) "r15"))

(test-case
 "Rosette validator memory comparison ignores candidate-only stack scratch writes"
 (define machine (new arm-machine% [config 13]))
 (send machine set-stack-scratch-config! 12 8 'downwards)
 (define printer (new arm-printer% [machine machine]))
 (define simulator (new arm-simulator-rosette% [machine machine]))
 (define validator
   (new arm-validator% [machine machine] [simulator simulator]))
 (define spec (encode printer "nop\n"))
 (define candidate (encode printer "strb r0, [r12, #-4]\n"))
 (define input (send machine get-state zero-init #:concrete #f))
 (vector-set! (progstate-regs input) 0 #xab)
 (vector-set! (progstate-regs input) 12 100)
 (define spec-out (send simulator interpret spec input))
 (define candidate-out (send simulator interpret candidate input spec-out))
 (check-not-exn
  (lambda ()
    (send validator assert-state-eq
          spec-out
          candidate-out
          (send printer encode-live '(memory))))))
