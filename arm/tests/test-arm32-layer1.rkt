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

(define (nzcv n z c v)
  (bitwise-ior (arithmetic-shift (if n 1 0) 3)
               (arithmetic-shift (if z 1 0) 2)
               (arithmetic-shift (if c 1 0) 1)
               (if v 1 0)))

(define (encode asm)
  (send printer encode (send parser ir-from-string asm)))

(define (inst-word asm)
  (arm-inst->word machine (vector-ref (encode asm) 0)))

(define (run asm regs [flags (nzcv #f #f #f #f)])
  (send simulator interpret
        (encode asm)
        (progstate (vector-copy regs) (progstate-memory base-state) flags)))

(define (r0 state)
  (vector-ref (progstate-regs state) 0))

(check-equal? (inst-word "adc r0, r1, r2\n") #xe0a10002)
(check-equal? (inst-word "adds r0, r1, r2\n") #xe0910002)
(check-equal? (inst-word "teq r1, r2\n") #xe1310002)
(check-equal? (inst-word "cmn r1, #1\n") #xe3710001)
(check-equal? (inst-word "movmi r0, r1\n") #x41a00001)

(let ([out (run "adcs r0, r1, r2\n"
                (vector 0 2 3 0)
                (nzcv #f #f #t #f))])
  (check-equal? (r0 out) 6)
  (check-equal? (progstate-z out) (nzcv #f #f #f #f)))

(let ([out (run "sbcs r0, r1, r2\n"
                (vector 0 5 3 0)
                (nzcv #f #f #f #f))])
  (check-equal? (r0 out) 1)
  (check-equal? (progstate-z out) (nzcv #f #f #t #f)))

(let ([out (run "adds r0, r1, #1\n"
                (vector 0 #x7fffffff 0 0)
                (nzcv #f #f #f #f))])
  (check-equal? (r0 out) (- #x80000000))
  (check-equal? (progstate-z out) (nzcv #t #f #f #t)))

(let ([out (run "cmn r1, #1\n"
                (vector 0 -1 0 0)
                (nzcv #f #f #f #f))])
  (check-equal? (progstate-z out) (nzcv #f #t #t #f)))

(let ([out (run "teq r1, r2\n"
                (vector 0 #x55 #x55 0)
                (nzcv #f #f #t #f))])
  (check-equal? (progstate-z out) (nzcv #f #t #t #f)))

(check-equal? (r0 (run "movcs r0, #7\n"
                       (vector 0 0 0 0)
                       (nzcv #f #f #t #f)))
              7)
(check-equal? (r0 (run "movcs r0, #7\n"
                       (vector 3 0 0 0)
                       (nzcv #f #f #f #f)))
              3)
(check-equal? (r0 (run "movgt r0, #9\n"
                       (vector 0 0 0 0)
                       (nzcv #f #f #f #f)))
              9)
(check-equal? (r0 (run "movgt r0, #9\n"
                       (vector 4 0 0 0)
                       (nzcv #f #t #f #f)))
              4)
