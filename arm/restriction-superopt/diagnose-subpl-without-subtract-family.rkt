#lang racket

(require "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-machine.rkt"
         "../arm-simulator-racket.rkt")

(define parser (new arm-parser%))
(define machine (new arm-machine% [config 4]))
(define printer (new arm-printer% [machine machine]))
(define simulator (new arm-simulator-racket% [machine machine]))

(define (encode asm)
  (send printer encode (send parser ir-from-string asm)))

(define original-subpl (encode "subpl r0, r1, r2\n"))
(define original-sub (encode "sub r0, r1, r2\n"))

(define regs-list
  (list (vector 100 5 3 0)
        (vector -9 -7 11 0)
        (vector 77 0 -1 0)
        (vector #x12345678 #x7fffffff 1 0)
        (vector 0 #x80000000 5 0)
        (vector 42 31 31 0)))

(define flags-list '(0 1 2 4 8 9 10 12 15))

(define (state regs flags)
  (define base
    (send machine get-state
          (lambda (#:min [min #f] #:max [max #f] #:const [const #f]) 0)))
  (progstate (vector-copy regs) (progstate-memory base) flags))

(define (u32 value)
  (bitwise-and value #xffffffff))

(define (popcount32 value)
  (for/sum ([bit (in-range 32)])
    (if (bitwise-bit-set? value bit) 1 0)))

(define (r0-cost expected actual)
  (popcount32
   (bitwise-xor (u32 (vector-ref (progstate-regs expected) 0))
                (u32 (vector-ref (progstate-regs actual) 0)))))

(define (program-cost original candidate)
  (for*/sum ([regs regs-list]
             [flags flags-list])
    (define input (state regs flags))
    (define expected (send simulator interpret original input))
    (define actual (send simulator interpret candidate input))
    (r0-cost expected actual)))

(define (line suffix op args)
  (format "~a~a ~a\n" op suffix args))

(define (mvn-add-add-candidate suffixes)
  (match-define (list mvn-suffix add-suffix add-imm-suffix) suffixes)
  (encode
   (string-append
    (line mvn-suffix "mvn" "r3, r2")
    (line add-suffix "add" "r0, r1, r3")
    (line add-imm-suffix "add" "r0, r0, #1"))))

(define choices '("" "pl"))

(displayln "subpl target: condition suffix variants for mvn/add/add#")
(for* ([mvn-suffix choices]
       [add-suffix choices]
       [add-imm-suffix choices])
  (define suffixes (list mvn-suffix add-suffix add-imm-suffix))
  (printf "~s\tcost=~a\n"
          suffixes
          (program-cost original-subpl
                        (mvn-add-add-candidate suffixes))))

(displayln "sub target: unpredicated mvn/add/add#")
(printf "cost=~a\n"
        (program-cost original-sub
                      (mvn-add-add-candidate '("" "" ""))))
