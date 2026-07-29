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

(define (run asm regs [flags 0])
  (send simulator interpret
        (encode asm)
        (progstate (vector-copy regs) (progstate-memory base-state) flags)))

(check-equal? (inst-word "swp r0, r2, [r1]\n") #xe1010092)
(check-equal? (inst-word "swpb r0, r2, [r1]\n") #xe1410092)
(check-equal? (inst-word "smlal r0, r1, r2, r3\n") #xe0e10392)
(check-equal? (inst-word "umlal r0, r1, r2, r3\n") #xe0a10392)
(check-equal? (inst-word "muls r0, r1, r2\n") #xe0100291)
(check-equal? (inst-word "mlas r0, r1, r2, r3\n") #xe0303291)
(check-equal? (inst-word "smulls r0, r1, r2, r3\n") #xe0d10392)
(check-equal? (inst-word "umulls r0, r1, r2, r3\n") #xe0910392)
(check-equal? (inst-word "smlals r0, r1, r2, r3\n") #xe0f10392)
(check-equal? (inst-word "umlals r0, r1, r2, r3\n") #xe0b10392)
(check-equal? (inst-word "ldm r1, #3\n") #xe8910003)
(check-equal? (inst-word "stm r1, #3\n") #xe8810003)

(let ([out (run "str r3, [r1, #0]\nswp r0, r2, [r1]\nldr r3, [r1, #0]\n"
                (vector 0 10 55 77))])
  (check-equal? (vector-ref (progstate-regs out) 0) 77)
  (check-equal? (vector-ref (progstate-regs out) 3) 55))

(let ([out (run "strb r3, [r1, #0]\nswpb r0, r2, [r1]\nldrb r3, [r1, #0]\n"
                (vector 0 10 #x1234 #xff))])
  (check-equal? (vector-ref (progstate-regs out) 0) #xff)
  (check-equal? (vector-ref (progstate-regs out) 3) #x34))

(let ([out (run "smlal r0, r1, r2, r3\n"
                (vector 5 0 2 3))])
  (check-equal? (vector-ref (progstate-regs out) 0) 11)
  (check-equal? (vector-ref (progstate-regs out) 1) 0))

(let ([out (run "muls r0, r1, r2\n"
                (vector 0 -1 2 0)
                3)])
  (check-equal? (vector-ref (progstate-regs out) 0) -2)
  (check-equal? (progstate-z out) 11))

(let ([out (run "mlas r0, r1, r2, r3\n"
                (vector 0 2 3 -6)
                2)])
  (check-equal? (vector-ref (progstate-regs out) 0) 0)
  (check-equal? (progstate-z out) 6))

(let ([out (run "smulls r0, r1, r2, r3\n"
                (vector 0 0 -2 3)
                3)])
  (check-equal? (vector-ref (progstate-regs out) 0) -6)
  (check-equal? (vector-ref (progstate-regs out) 1) -1)
  (check-equal? (progstate-z out) 11))

(let ([out (run "umlals r0, r1, r2, r3\n"
                (vector 0 0 0 3)
                2)])
  (check-equal? (vector-ref (progstate-regs out) 0) 0)
  (check-equal? (vector-ref (progstate-regs out) 1) 0)
  (check-equal? (progstate-z out) 6))

(let ([out (run "stm r3, #5\nmov r0, #0\nmov r2, #0\nldm r3, #5\n"
                (vector 11 0 22 100))])
  (check-equal? (vector-ref (progstate-regs out) 0) 11)
  (check-equal? (vector-ref (progstate-regs out) 2) 22))
