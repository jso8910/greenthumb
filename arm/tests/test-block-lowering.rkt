#lang racket

(require rackunit
         "../../memory-racket.rkt"
         "../arm-block-lowering.rkt"
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-simulator-racket.rkt"
         "../arm-simulator-rosette.rkt"
         "../arm-validator.rkt")

(define parser (new arm-parser%))
(define machine (new arm-machine% [config 16]))
(define printer (new arm-printer% [machine machine]))
(define simulator (new arm-simulator-racket% [machine machine]))

(define (store-word-bytes! memory address value)
  (for ([i (in-range 4)])
    (send memory store (+ address i)
          (bitwise-and (arithmetic-shift value (* -8 i)) #xff))))

(define (input-state)
  (define regs (vector 0 0 0 0 4 5 6 7 8 9 10 11 12 100 14 1000))
  (define memory (new memory-racket%))
  (store-word-bytes! memory 100 #x11111111)
  (store-word-bytes! memory 104 #x22222222)
  (store-word-bytes! memory 108 #x33333333)
  (store-word-bytes! memory 112 #x44444444)
  (progstate regs memory 0))

(define (parse-code source)
  (send parser ir-from-string source))

(define (run code state)
  (send simulator interpret (send printer encode code) state))

(define (reg state id)
  (vector-ref (progstate-regs state) id))

(test-case "ordinary pop lowers to equivalent scalar loads"
  (define original (parse-code "pop {r0, r1, r2}\n"))
  (define lowered (lower-block-transfers original '(0 1 2 13)))
  (define original-output (run original (input-state)))
  (define lowered-output (run lowered (input-state)))
  (for ([id '(0 1 2 13)])
    (check-equal? (reg lowered-output id) (reg original-output id))))

(test-case "dead pop-pc load is projected away but stack writeback is preserved"
  (define lowered
    (lower-block-transfers (parse-code "pop {r0, r1, r2, pc}\n") '(0 1 2 13)))
  (define syntax (with-output-to-string (lambda () (send printer print-syntax lowered))))
  (check-false (regexp-match? #rx"r15|pc" syntax))
  (check-regexp-match #rx"add r13, r13, #16" syntax)
  (define output (run lowered (input-state)))
  (check-equal? (reg output 0) #x11111111)
  (check-equal? (reg output 1) #x22222222)
  (check-equal? (reg output 2) #x33333333)
  (check-equal? (reg output 13) 116))

(test-case "lowering refuses to shift a later pc read"
  (check-exn
   #rx"PC-read instruction index"
   (lambda ()
     (lower-block-transfers
      (parse-code "pop {r1, r2, r3}\nmov r0, pc\n")
      '(0)))))

(test-case "lowered pop input states are generated inside GreenThumb"
  (define compressed-machine (new arm-machine% [config 5]))
  (define compressed-printer (new arm-printer% [machine compressed-machine]))
  (define compressed-parser (new arm-parser%))
  (define compressed-code
    (send compressed-printer encode
          (send compressed-parser ir-from-string
                "ldr r0, [r3, #0]\nldr r1, [r3, #4]\nldr r2, [r3, #8]\nadd r3, r3, #16\n")))
  (define validator
    (new arm-validator%
         [machine compressed-machine]
         [simulator (new arm-simulator-rosette% [machine compressed-machine])]
         [solver-name 'z3]))
  (check-equal? (length (send validator generate-input-states 8 compressed-code #f)) 8))
