#lang racket

(require "../machine.rkt" "../inst.rkt" "../special.rkt" "../ops-racket.rkt"
         "arm-restrictions.rkt")

(provide arm-machine% (all-defined-out))

;; Program states store ARM flags separately so liveness can distinguish
;; preserved flags from flags that an instruction actually reads or writes.
;; The 3-argument form is kept as a compatibility constructor for callers that
;; still pass packed NZCV in bit order 3..0.
(define (bool->flag-bit value)
  (cond
   [(boolean? value) (if value 1 0)]
   [else value]))

(define (flag-bit flags start end)
  (cond
   [(boolean? flags) flags]
   [(number? flags) (bitwise-bit-field flags start end)]
   [else flags]))

(define (pack-flag-fields n z c v)
  (cond
   [(and (boolean? n) (boolean? z) (boolean? c) (boolean? v))
    (or n z c v)]
   [else
    (bitwise-ior (arithmetic-shift (bool->flag-bit n) 3)
                 (arithmetic-shift (bool->flag-bit z) 2)
                 (arithmetic-shift (bool->flag-bit c) 1)
                 (bool->flag-bit v))]))

(define (progstate regs memory flags-or-n . maybe-zcv)
  (match maybe-zcv
    ['()
     (vector regs memory
             (flag-bit flags-or-n 3 4)
             (flag-bit flags-or-n 2 3)
             (flag-bit flags-or-n 1 2)
             (flag-bit flags-or-n 0 1))]
    [(list z c v)
     (vector regs memory flags-or-n z c v)]))

(define-syntax-rule (progstate-regs x) (vector-ref x 0))
(define-syntax-rule (progstate-memory x) (vector-ref x 1))
(define-syntax-rule (progstate-n x) (vector-ref x 2))
(define-syntax-rule (progstate-zf x) (vector-ref x 3))
(define-syntax-rule (progstate-c x) (vector-ref x 4))
(define-syntax-rule (progstate-v x) (vector-ref x 5))
(define (progstate-z x)
  (pack-flag-fields (progstate-n x) (progstate-zf x) (progstate-c x) (progstate-v x)))

(define-syntax-rule (set-progstate-regs! x v) (vector-set! x 0 v))
(define-syntax-rule (set-progstate-memory! x v) (vector-set! x 1 v))
(define-syntax-rule (set-progstate-n! x v) (vector-set! x 2 v))
(define-syntax-rule (set-progstate-zf! x v) (vector-set! x 3 v))
(define-syntax-rule (set-progstate-c! x v) (vector-set! x 4 v))
(define-syntax-rule (set-progstate-v! x v) (vector-set! x 5 v))
(define (set-progstate-z! x flags)
  (set-progstate-n! x (flag-bit flags 3 4))
  (set-progstate-zf! x (flag-bit flags 2 3))
  (set-progstate-c! x (flag-bit flags 1 2))
  (set-progstate-v! x (flag-bit flags 0 1)))

(define arm-machine%
  (class machine%
    (super-new)
    (inherit-field bitwidth random-input-bits config
                   opcodes opcode-pool nop-id argtypes-info classes-info
                   isa-restrictions)
    
    (inherit define-instruction-class init-machine-description finalize-machine-description
             define-progstate-type define-arg-type
             update-progstate-ins kill-outs update-classes-pool get-opcode-name)
    (override display-state get-constructor
              progstate-structure update-progstate-ins-load update-progstate-ins-store
              load-restrictions! restriction-word-allowed?
              inst-allowed? program-allowed?)
    (field [cmp-inst #f])
    (init-field [inst-choice-name #f])

    (define (get-constructor) arm-machine%)

    (define (load-restrictions! file)
      (set! isa-restrictions (load-arm-restrictions file)))

    (define (restriction-word-allowed? word)
      (arm-word-allowed? isa-restrictions word))

    (define (inst-allowed? my-inst)
      (or (not isa-restrictions)
          (arm-inst-allowed? isa-restrictions this my-inst)))

    (define (program-allowed? code)
      (or (not isa-restrictions)
          (arm-program-allowed? isa-restrictions this code)))

    (unless bitwidth (set! bitwidth 32))
    (set! random-input-bits bitwidth)
    
    ;; In ARM instructions, constant can have any value that can be produced by rotating an 8-bit value right by any even number of bits within a 32-bit word.

    (define perline 8)

    (define shf-inst-reg '(asr lsl lsr ror))
    (define shf-inst-imm '(asr# lsl# lsr# ror#))
    (define cond-opcodes '(eq ne cs cc mi pl vs vc hi ls ge lt gt le al))
    
    ;; Inform GreenThum that the 'op' field of 'inst' contains 3 categories of opcodes.
    ;; 0. base  1. conditional  2. optional shift
    (init-machine-description 3)

    ;; index 0 of inst-op = base opcode
    (define/public (get-base-opcode-id x)
      (vector-member x (vector-ref opcodes 0)))
    (define/public (get-base-opcode-name x)
      (vector-ref (vector-ref opcodes 0) x))
    
    ;; index 1 of inst-op = conditional opcode
    (define/public (get-cond-opcode-id x)
      (or (vector-member x (vector-ref opcodes 1)) -1))
    (define/public (get-cond-opcode-name x)
      (if (>= x 0) (vector-ref (vector-ref opcodes 1) x) '||))
    
    ;; index 2 of inst-op = optional shift
    (define/public (get-shf-opcode-id x)
      (or (vector-member x (vector-ref opcodes 2)) -1))
    (define/public (get-shf-opcode-name x)
      (if (>= x 0) (vector-ref (vector-ref opcodes 2) x) '||))

    ;;;;;;;;;;;;;;;;;;;;; program state ;;;;;;;;;;;;;;;;;;;;;;;;

    (define (progstate-structure)
      (progstate (for/vector ([i config]) 'reg)
                 ;; # of registers = config
                 ;; most block of code doesn't use all registers
                 ;; the smaller the number of registers, the faster the search
                 ;; printer needs to encode registers's name to numbers in [0,config)
                 (get-memory-type)
                 'n 'z 'c 'v  ;; NZCV condition flags
                 ))

    (define-progstate-type 'reg 
      #:get (lambda (state arg) (vector-ref (progstate-regs state) arg))
      #:set (lambda (state arg val) (vector-set! (progstate-regs state) arg val)))

    (define-progstate-type 'regs
      #:get (lambda (state) (progstate-regs state))
      #:set (lambda (state val)
              (if (boolean? val)
                  (let ([regs (progstate-regs state)])
                    (if (vector? regs)
                        (for ([i (in-range (vector-length regs))])
                             (vector-set! regs i val))
                        (set-progstate-regs!
                         state (make-vector config val))))
                  (set-progstate-regs! state val))))

    (define-progstate-type (get-memory-type)
      #:get (lambda (state) (progstate-memory state))
      #:set (lambda (state val) (set-progstate-memory! state val)))

    (define-progstate-type 'n
      #:get (lambda (state) (progstate-n state))
      #:set (lambda (state val) (set-progstate-n! state val))
      #:min 0 #:max 1)
    (define-progstate-type 'z
      #:get (lambda (state) (progstate-zf state))
      #:set (lambda (state val) (set-progstate-zf! state val))
      #:min 0 #:max 1)
    (define-progstate-type 'c
      #:get (lambda (state) (progstate-c state))
      #:set (lambda (state val) (set-progstate-c! state val))
      #:min 0 #:max 1)
    (define-progstate-type 'v
      #:get (lambda (state) (progstate-v state))
      #:set (lambda (state val) (set-progstate-v! state val))
      #:min 0 #:max 1)

    ;;;;;;;;;;;;;;;;;;;;; instruction classes ;;;;;;;;;;;;;;;;;;;;;;;;
    (define-arg-type 'reg (lambda (config) (range config)) #:progstate 'reg)
    (define-arg-type 'reg-sp (lambda (config) '()) #:progstate 'reg)
    (define-arg-type 'const (lambda (config) '(0 1)))
    (define-arg-type 'bool (lambda (config) '(0 1)))
    (define-arg-type 'bit
      (lambda (config)
        `(0 1 2 3 4 7 8 15 16 23 24 ,(sub1 bitwidth))))
    (define-arg-type 'addr (lambda (config) '(0 1 2 3 4)))
    (define-arg-type 'imm12 (lambda (config) '(0 1 2 3 4 7 8 15 16 31 255 4095)))
    (define-arg-type 'reglist (lambda (config) '(1 2 3 5 7 15)))
    
    (define-instruction-class 'nop '(nop))
    
    ;; reg = reg op reg
    (define-instruction-class 'rrr-commute
      (list '(mul smmul) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins '((1 2) (n z c v)) #:outs '(0) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-mul-s
	      (list '(muls) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg reg) ()) #:ins '((1 2) (n z c v)) #:outs '(0 n z) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf
	      (list '(add and orr eor) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2) (n z c v) (3)) #:outs '(0) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf-imm
	      (list '(add and orr eor) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2) (n z c v) (3)) #:outs '(0) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf-carry
	      (list '(adc) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf-imm-carry
	      (list '(adc) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf-s
	      (list '(adds) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2) (n z c v) (3)) #:outs '(0 n z c v) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf-imm-s
	      (list '(adds) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2) (n z c v) (3)) #:outs '(0 n z c v) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf-s-carry
	      (list '(adcs) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c v) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-shf-imm-s-carry
	      (list '(adcs) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c v) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-logical-s
	      (list '(ands orrs eors) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg reg) ()) #:ins '((1 2) (n z c v)) #:outs '(0 n z) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-logical-shf-s
	      (list '(ands orrs eors) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c) #:commute '(1 . 2))

	    (define-instruction-class 'rrr-commute-logical-shf-imm-s
	      (list '(ands orrs eors) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c) #:commute '(1 . 2))

    (define-instruction-class 'rrr
      (list '(asr lsl lsr ror sdiv udiv uxtah) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins '((1 2) (n z c v)) #:outs '(0))

	    (define-instruction-class 'rrr-shf
	      (list '(sub rsb bic orn) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2) (n z c v) (3)) #:outs '(0))

	    (define-instruction-class 'rrr-shf-imm
	      (list '(sub rsb bic orn) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2) (n z c v) (3)) #:outs '(0))

	    (define-instruction-class 'rrr-shf-carry
	      (list '(sbc rsc) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0))

	    (define-instruction-class 'rrr-shf-imm-carry
	      (list '(sbc rsc) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0))

	    (define-instruction-class 'rrr-shf-s
	      (list '(subs rsbs) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2) (n z c v) (3)) #:outs '(0 n z c v))

	    (define-instruction-class 'rrr-shf-imm-s
	      (list '(subs rsbs) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2) (n z c v) (3)) #:outs '(0 n z c v))

	    (define-instruction-class 'rrr-shf-s-carry
	      (list '(sbcs rscs) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c v))

	    (define-instruction-class 'rrr-shf-imm-s-carry
	      (list '(sbcs rscs) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c v))

	    (define-instruction-class 'rrr-logical-s
	      (list '(bics) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg reg) ()) #:ins '((1 2) (n z c v)) #:outs '(0 n z))

	    (define-instruction-class 'rrr-logical-shf-s
	      (list '(bics) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (reg)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c))

	    (define-instruction-class 'rrr-logical-shf-imm-s
	      (list '(bics) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg reg) () (bit)) #:ins '((1 2 c) (n z c v) (3)) #:outs '(0 n z c))

    ;; reg = reg op imm
	    (define-instruction-class 'rri
	      (list '(add# sub# rsb# and# orr# eor# bic# orn#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg const) ()) #:ins '((1 2) (n z c v)) #:outs '(0))

	    (define-instruction-class 'rri-carry
	      (list '(adc# sbc# rsc#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg const) ()) #:ins '((1 2 c) (n z c v)) #:outs '(0))

	    (define-instruction-class 'rri-s
	      (list '(adds# subs# rsbs#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg const) ()) #:ins '((1 2) (n z c v)) #:outs '(0 n z c v))

	    (define-instruction-class 'rri-s-carry
	      (list '(adcs# sbcs# rscs#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg const) ()) #:ins '((1 2 c) (n z c v)) #:outs '(0 n z c v))

	    (define-instruction-class 'rri-logical-s
	      (list '(ands# orrs# eors# bics#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg const) ()) #:ins '((1 2 c) (n z c v)) #:outs '(0 n z c))

    (define-instruction-class 'rrb
      (list '(asr# lsl# lsr# ror#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg bit) ()) #:ins '((1 2) (n z c v)) #:outs '(0))

    ;; reg = reg
    (define-instruction-class 'rr-shf
      (list '(mov mvn) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg) () (reg)) #:ins '((1) (n z c v) (2)) #:outs '(0))

    (define-instruction-class 'rr-shf-imm
      (list '(mov mvn) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg) () (bit)) #:ins '((1) (n z c v) (2)) #:outs '(0))

	    (define-instruction-class 'rr-shf-s
	      (list '(movs mvns) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg) ()) #:ins '((1) (n z c v)) #:outs '(0 n z))

	    (define-instruction-class 'rr-shf-s-shift
	      (list '(movs mvns) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #t)
	      #:args '((reg reg) () (reg)) #:ins '((1 c) (n z c v) (2)) #:outs '(0 n z c))

	    (define-instruction-class 'rr-shf-imm-s
	      (list '(movs mvns) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg) () (bit)) #:ins '((1 c) (n z c v) (2)) #:outs '(0 n z c))

    (define-instruction-class 'rr
      (list '(rev rev16 revsh rbit uxth uxtb clz) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg) ()) #:ins '((1) (n z c v)) #:outs '(0))

    ;; reg = imm
    (define-instruction-class 'ri1
      (list '(mov# mvn#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg const) ()) #:ins '((1) (n z c v)) #:outs '(0))

	    (define-instruction-class 'ri1-s
	      (list '(movs# mvns#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg const) ()) #:ins '((1 c) (n z c v)) #:outs '(0 n z c))

    (define-instruction-class 'ri2
      (list '(movw# movt#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg const) ()) #:ins '((0 1) (n z c v)) #:outs '(0))

    ;; reg = reg op reg op reg
    (define-instruction-class 'rrrr-commute
      (list '(mla smmla) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((1 2 3) (n z c v)) #:outs '(0) #:commute '(2 . 3))

	    (define-instruction-class 'rrrr-commute-s
	      (list '(mlas) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg reg reg) ()) #:ins '((1 2 3) (n z c v)) #:outs '(0 n z) #:commute '(2 . 3))

    (define-instruction-class 'rrrr
      (list '(mls smmls) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((1 2 3) (n z c v)) #:outs '(0))

    (define-instruction-class 'ddrr
      (list '(smull umull) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((2 3) (n z c v)) #:outs '(0 1) #:commute '(2 . 3))

	    (define-instruction-class 'ddrr-s
	      (list '(smulls umulls) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg reg reg) ()) #:ins '((2 3) (n z c v)) #:outs '(0 1 n z) #:commute '(2 . 3))

    (define-instruction-class 'ddrr-acc
      (list '(smlal umlal) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((0 1 2 3) (n z c v)) #:outs '(0 1) #:commute '(2 . 3))

	    (define-instruction-class 'ddrr-acc-s
	      (list '(smlals umlals) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg reg reg) ()) #:ins '((0 1 2 3) (n z c v)) #:outs '(0 1 n z) #:commute '(2 . 3))

    (define-instruction-class 'rrii
      (list '(bfi sbfx ubfx) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg bit bit) ()) #:ins '((1 2 3) (n z c v)) #:outs '(1))

    (define-instruction-class 'rii
      (list '(bfc) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg bit bit) ()) #:ins '((0 1 2) (n z c v)) #:outs '(0))

    (define-instruction-class 'load#
      (list '(ldr# ldrb# ldrh# ldrsb# ldrsh#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg-sp addr) ()) #:ins `((1 2 ,(get-memory-type)) (n z c v)) #:outs '(0))

    (define-instruction-class 'load
      (list '(ldr ldrb ldrh ldrsb ldrsh) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins `((1 2 ,(get-memory-type)) (n z c v)) #:outs '(0))

    (define-instruction-class 'store#
      (list '(str# strb# strh#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg-sp addr) ()) #:ins '((0 1 2) (n z c v)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'store
      (list '(str strb strh) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins '((0 1 2) (n z c v)) #:outs `(,(get-memory-type)))

    ;; Rust ARM32 raw transfer forms.  These expose P/U/W and shifted-register
    ;; offset fields that normal GreenThumb assembly syntax canonicalizes away.
    (define-instruction-class 'load-full-imm
      (list '(ldr-full# ldrb-full# ldrh-full# ldrsb-full# ldrsh-full#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg imm12 bool bool bool) ())
      #:ins `((1 2 3 4 5 ,(get-memory-type)) (n z c v)) #:outs '(0))

    (define-instruction-class 'store-full-imm
      (list '(str-full# strb-full# strh-full#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg imm12 bool bool bool) ())
      #:ins '((0 1 2 3 4 5) (n z c v)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'load-full-reg
      (list '(ldr-full ldrb-full) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg reg bool bool bool) () (bit))
      #:ins `((1 2 3 4 5 ,(get-memory-type)) (n z c v) (6)) #:outs '(0))

    (define-instruction-class 'store-full-reg
      (list '(str-full strb-full) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg reg bool bool bool) () (bit))
      #:ins '((0 1 2 3 4 5) (n z c v) (6)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'load-half-full-reg
      (list '(ldrh-full ldrsb-full ldrsh-full) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg bool bool bool) ())
      #:ins `((1 2 3 4 5 ,(get-memory-type)) (n z c v)) #:outs '(0))

    (define-instruction-class 'store-half-full-reg
      (list '(strh-full) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg bool bool bool) ())
      #:ins '((0 1 2 3 4 5) (n z c v)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'swp
      (list '(swp swpb) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins `((1 2 ,(get-memory-type)) (n z c v))
      #:outs `(0 ,(get-memory-type)))

    (define-instruction-class 'block-load
      (list '(ldm#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reglist) ()) #:ins `((0 ,(get-memory-type)) (n z c v)) #:outs '(regs))

    (define-instruction-class 'block-store
      (list '(stm#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reglist) ()) #:ins `((0 regs) (n z c v)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'block-load-full
      (list '(ldm-full#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reglist bool bool bool) ())
      #:ins `((0 1 2 3 4 ,(get-memory-type)) (n z c v)) #:outs '(regs))

    (define-instruction-class 'block-store-full
      (list '(stm-full#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reglist bool bool bool) ())
      #:ins `((0 1 2 3 4 regs) (n z c v)) #:outs `(,(get-memory-type)))

	    (define-instruction-class 'cmp-shf
	      (list '(cmp cmn) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #f)
	      #:args '((reg reg) () (reg)) #:ins '((0 1) (n z c v) (2)) #:outs '(n z c v))

	    (define-instruction-class 'cmp-shf-imm
	      (list '(cmp cmn) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg) () (bit)) #:ins '((0 1) (n z c v) (2)) #:outs '(n z c v))

	    (define-instruction-class 'test
	      (list '(tst teq) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg reg) ()) #:ins '((0 1) (n z c v)) #:outs '(n z))

	    (define-instruction-class 'test-shf
	      (list '(tst teq) cond-opcodes shf-inst-reg)
	      #:required '(#t #f #t)
	      #:args '((reg reg) () (reg)) #:ins '((0 1 c) (n z c v) (2)) #:outs '(n z c))

	    (define-instruction-class 'test-shf-imm
	      (list '(tst teq) cond-opcodes shf-inst-imm)
	      #:required '(#t #f #t)
	      #:args '((reg reg) () (bit)) #:ins '((0 1 c) (n z c v) (2)) #:outs '(n z c))

	    (define-instruction-class 'cmpi
	      (list '(cmp# cmn#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg const) ()) #:ins '((0 1) (n z c v)) #:outs '(n z c v))

	    (define-instruction-class 'testi
	      (list '(tst# teq#) cond-opcodes)
	      #:required '(#t #f)
	      #:args '((reg const) ()) #:ins '((0 1 c) (n z c v)) #:outs '(n z c))

    (finalize-machine-description)
    
    (set! cmp-inst (map (lambda (x) (get-base-opcode-id x))
                         '(cmp tst teq cmn cmp# tst# teq# cmn#
                           adds adcs subs rsbs sbcs rscs ands orrs eors bics
                           adds# adcs# subs# rsbs# sbcs# rscs# ands# orrs# eors# bics#
                           movs mvns movs# mvns#
                           muls mlas smulls umulls smlals umlals)))
    
    (define (print-line v)
      (define count 0)
      (for ([i v])
           (when (= count perline)
	     (newline)
	     (set! count 0))
           (display i)
           (display " ")
           (set! count (add1 count))
           )
      (newline)
      )

    ;; Pretty print progstate.
    (define (display-state s)
      (pretty-display "REGS:")
      (print-line (progstate-regs s))
      (pretty-display "MEMORY:")
      (pretty-display (progstate-memory s))
      (pretty-display (format "Z: ~a" (progstate-z s)))
      )

    ;; overridden method.
    ;; Remove code that behaves like nop.
    (define/override (clean-code code [prefix (vector)])
      ;; Filter out nop.
      (vector-filter-not
       (lambda (x) (= (vector-ref (inst-op x) 0) (vector-ref nop-id 0)))
       code))

    ;; Analyze input code and choose the instruction set available during
    ;; synthesis.  Keep this as a correctness-oriented superset: opcode
    ;; usefulness is a proposal-bias concern, not a hard reachability gate.
    (define/override (analyze-opcode prefix code postfix)
      (define unmodeled-rosette-opcodes
        '(ldm-full# stm-full#))
      (define modeled-opcodes
        (filter-not
         (lambda (opcode-name) (member opcode-name unmodeled-rosette-opcodes))
         (vector->list (vector-ref opcodes 0))))
      (set! inst-choice-name modeled-opcodes)
      (when debug (pretty-display `(inst-choice all-modeled)))
      (set! opcode-pool
            (filter
             (lambda (ops-vec)
               (member (get-base-opcode-name (vector-ref ops-vec 0))
                       modeled-opcodes))
             opcode-pool))
      (update-classes-pool)
      ;;(pretty-display (map (lambda (x) (get-opcode-name x)) opcode-pool))
      )

    ;; Helper function for 'analyze-opcode'.
    (define (code-has code inst-list)
      (for/or ([i code])
              (let ([opcode-name (get-base-opcode-name (vector-ref (inst-op i) 0))])
                (member opcode-name inst-list))))

    (define/override (reset-opcode-pool) 
      (set! opcode-pool (flatten (for/list ([info classes-info]) (instclass-opcodes info)))))

    ;; Analyze input code and update operands' ranges.
    (define/override (analyze-args prefix code postfix live-in live-out)
      ;; set e list to empty
      (define type-reg (hash-ref argtypes-info 'reg))
      (set-argtype-valid! type-reg (list))

      ;; collect from context
      (super analyze-args prefix (vector) postfix live-in live-out)
      (define context-reg-list (argtype-valid type-reg))
      (set-argtype-valid! type-reg (list))

      ;;; collect from code
      (super analyze-args (vector) code (vector) live-in live-out)
      (define reg-list (argtype-valid type-reg))

      (define (reglist-regs my-inst)
        (define opcode-name (get-base-opcode-name (vector-ref (inst-op my-inst) 0)))
        (define args (inst-args my-inst))
        (if (and (member opcode-name '(ldm# stm# ldm-full# stm-full#))
                 (>= (vector-length args) 2))
            (let ([mask (vector-ref args 1)])
              (for/list ([reg-id (in-range 16)]
                         #:when (= (bitwise-bit-field mask reg-id (add1 reg-id)) 1))
                        reg-id))
            '()))

      (set! reg-list
            (remove-duplicates
             (append reg-list
                     (flatten
                      (for/list ([my-inst (vector-append prefix code postfix)])
                                (reglist-regs my-inst))))))
      
      (define type-reg-sp (hash-ref argtypes-info 'reg-sp))
      (define reg-sp-list (argtype-valid type-reg-sp))

      (set! reg-list (remove-duplicates (append reg-list reg-sp-list)))
      (set-argtype-valid! type-reg reg-list)
      (set-argtype-valid! type-reg-sp
                          (remove-duplicates (append reg-sp-list reg-list)))

      (define exclude (append reg-list context-reg-list))
      
      ;; If there are too few regs, add one more.
      ;; But try to add one that does not use anywhere
      ;; (including prefix and postfix).
      (when (<= (length reg-list) 2)
            (let ([add-reg
                   (for/or ([i config])
                           (and (not (member i exclude)) i))])
              (when add-reg (set-argtype-valid! type-reg (cons add-reg reg-list)))))
      
      (for ([pair (hash->list argtypes-info)])
           (let ([name (car pair)]
                 [info (cdr pair)])
             (pretty-display `(ARM-ARG ,name ,(argtype-valid info)))))
      )

    ;; Inform about the order of argument for load instruction
    (define (update-progstate-ins-load my-inst addr mem state-base)
      (define op (vector-ref (inst-op my-inst) 0))
      (define opcode-name (get-base-opcode-name op))
      (define args (inst-args my-inst))
      (cond
       [(equal? 'ldr# opcode-name)
        (define offset (vector-ref args 2))
        (update-progstate-ins
         my-inst (list (finitize (- addr offset) bitwidth) offset mem) state-base)]
       [(equal? 'ldr opcode-name)
        (define fp (vector-ref (progstate-regs state-base) (vector-ref args 1)))
        (define offset (vector-ref (progstate-regs state-base) (vector-ref args 2)))

        (cond
         [fp
          (update-progstate-ins
           my-inst (list fp (finitize (- addr fp) bitwidth) mem) state-base)]
         [offset
          (update-progstate-ins
           my-inst (list (finitize (- addr offset) bitwidth) offset mem) state-base)]
         [else
          (for/list ([v (arithmetic-shift 1 bitwidth)])
                    (let ([vv (finitize v bitwidth)])
                      (update-progstate-ins
                       my-inst (list vv (finitize (- addr vv) bitwidth) mem) state-base)))])]
       [else (raise (format "update-progstate-ins-load: unknown instruction ~a" opcode-name))]))

    ;; Inform about the order of argument for store instruction
    (define (update-progstate-ins-store my-inst addr val state)
      ;; Put val before addr => arg 0 is val, arg 1 is address.
      (define op (vector-ref (inst-op my-inst) 0))
      (define opcode-name (get-base-opcode-name op))
      (define args (inst-args my-inst))
      (define offset (vector-ref args 2))
      (cond
       [(equal? 'str# opcode-name)
        (update-progstate-ins
         my-inst (list val (finitize (- addr offset) bitwidth) offset) state)]
       [(equal? 'str opcode-name)
        (define fp (vector-ref (progstate-regs state) (vector-ref args 1)))
        (set! offset (vector-ref (progstate-regs state) offset))

        (cond
         [fp
          (update-progstate-ins
           my-inst (list val fp (finitize (- addr fp) bitwidth)) state)]
         [offset
          (update-progstate-ins
           my-inst (list val (finitize (- addr offset) bitwidth) offset) state)]
         [else
          (for/list ([v (arithmetic-shift 1 bitwidth)])
                    (let ([vv (finitize v bitwidth)])
                      (update-progstate-ins
                       my-inst (list val vv (finitize (- addr vv) bitwidth)) state)))])]
       [else (raise (format "update-progstate-ins-store: unknown instruction ~a" opcode-name))]))
                          
    ))
