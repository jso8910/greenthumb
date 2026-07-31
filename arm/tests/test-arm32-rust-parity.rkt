#lang racket

(require rackunit
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-restrictions.rkt"
         "../arm-simulator-racket.rkt"
         "../../inst.rkt")

(define parser (new arm-parser%))
(define machine (new arm-machine% [config 16]))
(define simulator (new arm-simulator-racket% [machine machine]))

(define (base-state)
  (send machine get-state
        (lambda (#:min [min #f] #:max [max #f] #:const [const #f])
          (or const 0))))

(define (op-id op [cond '||] [shf '||])
  (send machine get-opcode-id (vector op cond shf)))

(define (mk op args #:cond [cond '||] #:shf [shf '||])
  (inst (op-id op cond shf) (list->vector args)))

(define (inst-word my-inst)
  (arm-inst->word machine my-inst))

(define (run code regs [flags 0] [memory #f])
  (send simulator interpret
        (list->vector code)
        (progstate (vector-copy regs)
                   (or memory (progstate-memory (base-state)))
                   flags)))

(define (store-word-bytes! memory address value)
  (for ([i (in-range 4)])
    (send memory store (+ address i)
          (bitwise-and (arithmetic-shift value (* -8 i)) #xff))))

(check-exn exn:fail?
           (lambda () (send parser ir-from-string "b #1\n")))
(check-exn exn:fail?
           (lambda () (send parser ir-from-string "bl #1\n")))
(check-exn exn:fail?
           (lambda () (send parser ir-from-string "bx r0\n")))
(check-exn exn:fail?
           (lambda () (send parser ir-from-string "bne #1\n")))
(check-exn exn:fail?
           (lambda () (send parser ir-from-string "b .LBB0_1\n")))

(check-equal? (inst-word (mk 'ldr-full# '(0 1 12 1 0 1))) #xe531000c)
(check-equal? (inst-word (mk 'strb-full '(2 3 4 1 1 0 2) #:shf 'lsl#)) #xe7c32104)
(check-equal? (inst-word (mk 'ldrh-full# '(0 1 2 1 1 0))) #xe1d100b2)
(check-equal? (inst-word (mk 'stm-full# '(3 5 1 0 1))) #xe9230005)
(check-equal? (inst-word (mk 'ldm-full# '(3 5 0 1 1))) #xe8b30005)

(check-false (inst-word (mk 'ldm-full# '(15 5 0 1 0))))
(check-false (inst-word (mk 'stm-full# '(3 0 0 1 0))))
(check-false (inst-word (mk 'swp '(15 1 2))))
(check-false (inst-word (mk 'ldr-full# '(0 15 4 0 1 0))))

(let ([out (run (list (mk 'str-full# '(2 1 4 0 1 0))
                      (mk 'ldrb-full# '(3 1 1 1 0 0)))
                (vector 0 100 #x12345678 0 0 0 0 0 0 0 0 0 0 0 0 1000))])
  (check-equal? (vector-ref (progstate-regs out) 1) 104)
  (check-equal? (vector-ref (progstate-regs out) 3) #x12))

(let* ([memory (progstate-memory (base-state))]
       [_ (store-word-bytes! memory 100 #x11223344)]
       [out (run (list (mk 'ldm-full# '(3 8 0 1 1)))
                 (vector 0 0 0 100 0 0 0 0 0 0 0 0 0 0 0 1000)
                 0
                 memory)])
  (check-equal? (vector-ref (progstate-regs out) 3) #x11223344))

(let ([out (run (list (mk 'stm-full# '(3 5 1 0 1)))
                (vector 11 22 33 100 0 0 0 0 0 0 0 0 0 0 0 1000))])
  (check-equal? (vector-ref (progstate-regs out) 3) 92)
  (check-equal? (send (progstate-memory out) lookup-update 92) 11)
  (check-equal? (send (progstate-memory out) lookup-update 96) 33))
