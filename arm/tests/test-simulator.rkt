#lang s-exp rosette

(require "../arm-machine.rkt"
         "../arm-printer.rkt" "../arm-parser.rkt"
         "../arm-simulator-rosette.rkt" 
         "../arm-simulator-racket.rkt"
         "../arm-validator.rkt"
         "../arm-symbolic.rkt"
         "../../inst.rkt"
         "../../memory-rosette.rkt"
         )

(current-bitwidth 32)
(define parser (new arm-parser%))
(define machine (new arm-machine% [config 4])) ;; argument = (list num-regs memory)
(define printer (new arm-printer% [machine machine]))
(define simulator-racket (new arm-simulator-racket% [machine machine]))
(define simulator-rosette (new arm-simulator-rosette% [machine machine]))
(define validator (new arm-validator% [machine machine] [simulator simulator-rosette]))

(define pc-machine (new arm-machine% [config 16]))
(define pc-simulator-racket (new arm-simulator-racket% [machine pc-machine]))
(define pc-simulator-rosette (new arm-simulator-rosette% [machine pc-machine]))
(define (pc-mk op cond shf args)
  (inst (send pc-machine get-opcode-id (vector op cond shf))
        (list->vector args)))
(define pc-code
  (vector
   (pc-mk 'add '|| '|| '(1 1 0))
   (pc-mk 'add '|| '|| '(2 2 15))))
(define pc-state
  (progstate (vector 5 10 20 0 0 0 0 0 0 0 0 0 0 0 0 1000)
             #f
             0))
(define pc-output-racket (send pc-simulator-racket interpret pc-code pc-state))
(define pc-output-rosette (send pc-simulator-rosette interpret pc-code pc-state))
(define pc-regs-racket (progstate-regs pc-output-racket))
(define pc-regs-rosette (progstate-regs pc-output-rosette))
(unless (= (vector-ref pc-regs-racket 2) (vector-ref pc-regs-rosette 2))
  (raise "Racket/Rosette PC-read outputs differ"))
(unless (= (vector-ref pc-regs-racket 2) 1024)
  (raise "PC read did not include instruction-index offset"))
(unless (and (= (vector-ref pc-regs-racket 15) 1000)
             (= (vector-ref pc-regs-rosette 15) 1000))
  (raise "PC base register was mutated"))

(define (func-rand #:min [min #f] #:max [max #f] #:const [const #f])
  (if const const (random 10)))

(define (func-sym #:min [min #f] #:max [max #f] #:const [const #f])
  (define-symbolic* input number?)
  (if const const input))

;; Input machine state
#;(define input-state (progstate (vector 0 1 0 0)
                               (new memory-rosette% [get-fresh-val func-sym]) -1))
(define input-state (send machine get-state func-sym))

;; Section 1: Concrete program

(define code
(send parser ir-from-string "
rsb r1, r0, r0, lsr 1
orr r0, r0, r1, asr 31
"))

(send printer print-struct code)
(define encoded-code (send printer encode code))
(send printer print-struct encoded-code)
;;(send printer print-syntax (send printer decode encoded-code))

(define symbolic (new arm-symbolic% [machine machine] [printer printer]
                      [parser parser]
                      [validator validator] [simulator simulator-rosette]))
(define cost
  (send simulator-rosette performance-cost
        (for/vector ([i 2]) (send symbolic gen-sym-inst))))
(define output-state
  (send simulator-rosette interpret (for/vector ([i 2]) (send symbolic gen-sym-inst)) input-state))

#|
(define output-state
  (send simulator-rosette interpret encoded-code input-state))
(pretty-display ">>> Input.")
(send machine display-state input-state)
(newline)
(pretty-display ">>> Output from simulator in rosette.")
(send machine display-state output-state)
(define mem1 (progstate-memory output-state))
(send mem1 lookup-update 0)

(define output-state2
  (send simulator-rosette interpret encoded-code input-state output-state))
(newline)
(pretty-display ">>> Output2 from simulator in rosette.")
(send machine display-state output-state2)
(send validator assert-state-eq output-state output-state2 (send printer encode-live '(0)))
|#

;; (pretty-display
;;  (send enum abstract 
;;        (send machine progstate->vector output-state) (list 0 2 3 4) 8))
;; (newline)

;;(send simulator-racket performance-cost encoded-code)


;; ;; Section 3: Symbolic inputs
;; ;; Concrete program with symbolic inputs
#|
(define (sym-input)
  (define-symbolic* in number?)
  in)
(define input-state-sym (default-state machine sym-input))

(pretty-display "Interpret concrete program with symbolic inputs...")
(define output-state-sym
  (send simulator-rosette interpret encoded-code input-state-sym))
(send machine display-state output-state-sym)|#
