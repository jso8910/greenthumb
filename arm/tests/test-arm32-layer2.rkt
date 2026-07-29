#lang racket

(require rackunit
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-restrictions.rkt"
         "../arm-simulator-racket.rkt")

(define parser (new arm-parser%))
(define machine (new arm-machine% [config 4]))
(define printer (new arm-printer% [machine machine]))
(define simulator (new arm-simulator-racket% [machine machine]))
(define base-state
  (send machine get-state
        (lambda (#:min [min #f] #:max [max #f] #:const [const #f])
          (or const 0))))

(define (encode asm)
  (send printer encode (send parser ir-from-string asm)))

(define (inst-word asm)
  (arm-inst->word machine (vector-ref (encode asm) 0)))

(define (run asm regs)
  (send simulator interpret
        (encode asm)
        (progstate (vector-copy regs) (progstate-memory base-state) 0)))

(check-equal? (inst-word "ldrb r0, [r1, #3]\n") #xe5d10003)
(check-equal? (inst-word "strb r0, [r1, #3]\n") #xe5c10003)
(check-equal? (inst-word "ldrh r0, [r1, #2]\n") #xe1d100b2)
(check-equal? (inst-word "ldrsh r0, [r1, #2]\n") #xe1d100f2)
(check-equal? (inst-word "ldrsb r0, [r1, r2]\n") #xe19100d2)

(let ([out (run "str r0, [r1, r3]\nldr r2, [r1, r3]\n"
                (vector 1234 10 0 7))])
  (check-equal? (vector-ref (progstate-regs out) 2) 1234))

(let ([out (run "strb r0, [r1, #3]\nldrsb r2, [r1, #3]\n"
                (vector #xff 10 0 0))])
  (check-equal? (vector-ref (progstate-regs out) 2) -1))

(let ([out (run "strh r0, [r1, #4]\nldrsh r2, [r1, #4]\n"
                (vector #x8001 10 0 0))])
  (check-equal? (vector-ref (progstate-regs out) 2) -32767))

(let ([out (run "strh r0, [r1, #4]\nldrh r2, [r1, #4]\n"
                (vector #x8001 10 0 0))])
  (check-equal? (vector-ref (progstate-regs out) 2) #x8001))
