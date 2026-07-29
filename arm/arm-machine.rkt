#lang racket

(require "../machine.rkt" "../inst.rkt" "../special.rkt" "../ops-racket.rkt"
         "arm-restrictions.rkt")

(provide arm-machine% (all-defined-out))

;; define progstate macro
(define-syntax-rule
  (progstate regs memory z)
  (vector regs memory z))

(define-syntax-rule (progstate-regs x) (vector-ref x 0))
(define-syntax-rule (progstate-memory x) (vector-ref x 1))
(define-syntax-rule (progstate-z x) (vector-ref x 2))

(define-syntax-rule (set-progstate-regs! x v) (vector-set! x 0 v))
(define-syntax-rule (set-progstate-memory! x v) (vector-set! x 1 v))
(define-syntax-rule (set-progstate-z! x v) (vector-set! x 2 v))

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
                 'z  ;; conditoinal flag
                 ))

    (define-progstate-type 'reg 
      #:get (lambda (state arg) (vector-ref (progstate-regs state) arg))
      #:set (lambda (state arg val) (vector-set! (progstate-regs state) arg val)))

    (define-progstate-type 'regs
      #:get (lambda (state) (progstate-regs state))
      #:set (lambda (state val) (set-progstate-regs! state val)))

    (define-progstate-type (get-memory-type)
      #:get (lambda (state) (progstate-memory state))
      #:set (lambda (state val) (set-progstate-memory! state val)))

    ;; z stores packed NZCV flags as a 4-bit integer:
    ;; bit 3 = N, bit 2 = Z, bit 1 = C, bit 0 = V.
    (define-progstate-type 'z
      #:get (lambda (state) (progstate-z state))
      #:set (lambda (state val) (set-progstate-z! state val))
      #:min 0 #:max 15
      )

    ;;;;;;;;;;;;;;;;;;;;; instruction classes ;;;;;;;;;;;;;;;;;;;;;;;;
    (define-arg-type 'reg (lambda (config) (range config)) #:progstate 'reg)
    (define-arg-type 'reg-sp (lambda (config) '()) #:progstate 'reg)
    (define-arg-type 'const (lambda (config) '(0 1)))
    (define-arg-type 'bit (lambda (config) `(0 1 ,(sub1 bitwidth))))
    (define-arg-type 'addr (lambda (config) '()))
    (define-arg-type 'reglist (lambda (config) '(1 2 3 5 7 15)))
    
    (define-instruction-class 'nop '(nop))
    
    ;; reg = reg op reg
    (define-instruction-class 'rrr-commute
      (list '(mul smmul) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins '((1 2) (z 0)) #:outs '(0) #:commute '(1 . 2))

    (define-instruction-class 'rrr-commute-mul-s
      (list '(muls) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins '((1 2 z) (z 0)) #:outs '(0 z) #:commute '(1 . 2))

    (define-instruction-class 'rrr-commute-shf
      (list '(add adc and orr eor) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg reg) () (reg)) #:ins '((1 2) (z 0) (3)) #:outs '(0) #:commute '(1 . 2))

    (define-instruction-class 'rrr-commute-shf-imm
      (list '(add adc and orr eor) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg reg) () (bit)) #:ins '((1 2) (z 0) (3)) #:outs '(0) #:commute '(1 . 2))

    (define-instruction-class 'rrr-commute-shf-s
      (list '(adds adcs ands orrs eors) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg reg) () (reg)) #:ins '((1 2 z) (z 0) (3)) #:outs '(0 z) #:commute '(1 . 2))

    (define-instruction-class 'rrr-commute-shf-imm-s
      (list '(adds adcs ands orrs eors) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg reg) () (bit)) #:ins '((1 2 z) (z 0) (3)) #:outs '(0 z) #:commute '(1 . 2))

    (define-instruction-class 'rrr
      (list '(asr lsl lsr ror sdiv udiv uxtah) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins '((1 2) (z 0)) #:outs '(0))

    (define-instruction-class 'rrr-shf
      (list '(sub rsb sbc rsc bic orn) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg reg) () (reg)) #:ins '((1 2) (z 0) (3)) #:outs '(0))

    (define-instruction-class 'rrr-shf-imm
      (list '(sub rsb sbc rsc bic orn) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg reg) () (bit)) #:ins '((1 2) (z 0) (3)) #:outs '(0))

    (define-instruction-class 'rrr-shf-s
      (list '(subs rsbs sbcs rscs bics) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg reg) () (reg)) #:ins '((1 2 z) (z 0) (3)) #:outs '(0 z))

    (define-instruction-class 'rrr-shf-imm-s
      (list '(subs rsbs sbcs rscs bics) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg reg) () (bit)) #:ins '((1 2 z) (z 0) (3)) #:outs '(0 z))

    ;; reg = reg op imm
    (define-instruction-class 'rri
      (list '(add# adc# sub# rsb# sbc# rsc# and# orr# eor# bic# orn#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg const) ()) #:ins '((1 2) (z 0)) #:outs '(0))

    (define-instruction-class 'rri-s
      (list '(adds# adcs# subs# rsbs# sbcs# rscs# ands# orrs# eors# bics#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg const) ()) #:ins '((1 2 z) (z 0)) #:outs '(0 z))

    (define-instruction-class 'rrb
      (list '(asr# lsl# lsr# ror#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg bit) ()) #:ins '((1 2) (z 0)) #:outs '(0))

    ;; reg = reg
    (define-instruction-class 'rr-shf
      (list '(mov mvn) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg) () (reg)) #:ins '((1) (z 0) (2)) #:outs '(0))

    (define-instruction-class 'rr-shf-imm
      (list '(mov mvn) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg) () (bit)) #:ins '((1) (z 0) (2)) #:outs '(0))

    (define-instruction-class 'rr-shf-s
      (list '(movs mvns) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg) () (reg)) #:ins '((1 z) (z 0) (2)) #:outs '(0 z))

    (define-instruction-class 'rr-shf-imm-s
      (list '(movs mvns) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg) () (bit)) #:ins '((1 z) (z 0) (2)) #:outs '(0 z))

    (define-instruction-class 'rr
      (list '(rev rev16 revsh rbit uxth uxtb clz) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg) ()) #:ins '((1) (z 0)) #:outs '(0))

    ;; reg = imm
    (define-instruction-class 'ri1
      (list '(mov# mvn#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg const) ()) #:ins '((1) (z 0)) #:outs '(0))

    (define-instruction-class 'ri1-s
      (list '(movs# mvns#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg const) ()) #:ins '((1 z) (z 0)) #:outs '(0 z))

    (define-instruction-class 'ri2
      (list '(movw# movt#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg const) ()) #:ins '((0 1) (z 0)) #:outs '(0))

    ;; reg = reg op reg op reg
    (define-instruction-class 'rrrr-commute
      (list '(mla smmla) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((1 2 3) (z 0)) #:outs '(0) #:commute '(2 . 3))

    (define-instruction-class 'rrrr-commute-s
      (list '(mlas) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((1 2 3 z) (z 0)) #:outs '(0 z) #:commute '(2 . 3))

    (define-instruction-class 'rrrr
      (list '(mls smmls) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((1 2 3) (z 0)) #:outs '(0))

    (define-instruction-class 'ddrr
      (list '(smull umull) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((2 3) (z 0)) #:outs '(0 1) #:commute '(2 . 3))

    (define-instruction-class 'ddrr-s
      (list '(smulls umulls) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((2 3 z) (z 0)) #:outs '(0 1 z) #:commute '(2 . 3))

    (define-instruction-class 'ddrr-acc
      (list '(smlal umlal) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((0 1 2 3) (z 0)) #:outs '(0 1) #:commute '(2 . 3))

    (define-instruction-class 'ddrr-acc-s
      (list '(smlals umlals) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg reg) ()) #:ins '((0 1 2 3 z) (z 0)) #:outs '(0 1 z) #:commute '(2 . 3))

    (define-instruction-class 'rrii
      (list '(bfi sbfx ubfx) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg bit bit) ()) #:ins '((1 2 3) (z 0)) #:outs '(1))

    (define-instruction-class 'rii
      (list '(bfc) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg bit bit) ()) #:ins '((0 1 2) (z)) #:outs '(0))

    (define-instruction-class 'load#
      (list '(ldr# ldrb# ldrh# ldrsb# ldrsh#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg-sp addr) ()) #:ins `((1 2 ,(get-memory-type)) (z 0)) #:outs '(0))

    (define-instruction-class 'load
      (list '(ldr ldrb ldrh ldrsb ldrsh) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins `((1 2 ,(get-memory-type)) (z 0)) #:outs '(0))

    (define-instruction-class 'store#
      (list '(str# strb# strh#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg-sp addr) ()) #:ins '((0 1 2) (z)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'store
      (list '(str strb strh) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins '((0 1 2) (z)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'swp
      (list '(swp swpb) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reg reg) ()) #:ins `((1 2 ,(get-memory-type)) (z 0))
      #:outs `(0 ,(get-memory-type)))

    (define-instruction-class 'block-load
      (list '(ldm#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reglist) ()) #:ins `((0 ,(get-memory-type)) (z 0)) #:outs '(regs))

    (define-instruction-class 'block-store
      (list '(stm#) cond-opcodes)
      #:required '(#t #f)
      #:args '((reg reglist) ()) #:ins `((0 regs) (z)) #:outs `(,(get-memory-type)))

    (define-instruction-class 'cmp-shf
      (list '(tst teq cmp cmn) cond-opcodes shf-inst-reg)
      #:required '(#t #f #f)
      #:args '((reg reg) () (reg)) #:ins '((0 1 z) (z 0) (2)) #:outs '(z))

    (define-instruction-class 'cmp-shf-imm
      (list '(tst teq cmp cmn) cond-opcodes shf-inst-imm)
      #:required '(#t #f #t)
      #:args '((reg reg) () (bit)) #:ins '((0 1 z) (z 0) (2)) #:outs '(z))

    (define-instruction-class 'cmpi '(tst# teq# cmp# cmn#)
      #:args '(reg const) #:ins '(0 1 z) #:outs '(z))

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

    ;; Analyze input code and remove some opcodes from instuction pool to be used during synthesis.
    (define/override (analyze-opcode prefix code postfix)
      (set! code (vector-append prefix code postfix))
      (define inst-choice '(nop 
                            add adc sub rsb sbc rsc
                            add# adc# sub# rsb# sbc# rsc#
                            mov mvn
                            mov# mvn#
                            asr lsl lsr ror
                            asr# lsl# lsr# ror#))
                                
      (when (code-has code '(clz
                             and orr eor bic orn
                             and# orr# eor# bic# orn#
                             ands orrs eors bics
                             ands# orrs# eors# bics#
                             ))
            (set! inst-choice (append inst-choice '(clz
                                                    and orr eor bic orn
                                                    and# orr# eor# bic# orn#
                                                    ands orrs eors bics
                                                    ands# orrs# eors# bics#
                                                    ))))

      (when (code-has code '(adds adcs subs rsbs sbcs rscs
                             adds# adcs# subs# rsbs# sbcs# rscs#
                             movs mvns movs# mvns#
                             teq cmn teq# cmn#))
            (set! inst-choice
                  (append inst-choice
                          '(adds adcs subs rsbs sbcs rscs
                            adds# adcs# subs# rsbs# sbcs# rscs#
                            movs mvns movs# mvns#
                            teq cmn teq# cmn#))))
                                
      (when (code-has code '(movw# movt#))
            (set! inst-choice (append inst-choice '(movw# movt#))))

      (when (code-has code '(rev rev16 revsh rbit
        			 uxtah uxth uxtb
        			 bfc bfi
        			 sbfx ubfx
        			 ))
            (set! inst-choice (append inst-choice '(rev rev16 revsh rbit
        					    	uxtah uxth uxtb
        					    	bfc bfi
        					    	sbfx ubfx
        						))))
      (when (code-has code '(mul muls mla mlas mls
                                 smull umull smulls umulls smlal umlal smlals umlals
                                 smmul smmla smmls))
            (set! inst-choice (append inst-choice '(mul muls mla mlas mls
                                                        smull umull smulls umulls
                                                        smlal umlal smlals umlals
                                                        smmul smmla smmls))))
      (when (code-has code '(sdiv udiv))
            (set! inst-choice (append inst-choice '(sdiv udiv))))
      (when (code-has code '(ldr# ldr ldrb# ldrb ldrh# ldrh ldrsb# ldrsb ldrsh# ldrsh))
            (set! inst-choice (append inst-choice '(ldr# ldr ldrb# ldrb
                                                    ldrh# ldrh ldrsb# ldrsb ldrsh# ldrsh))))
      (when (code-has code '(str# str strb# strb strh# strh))
            (set! inst-choice (append inst-choice '(str# str strb# strb strh# strh))))
      (when (code-has code '(swp swpb))
            (set! inst-choice (append inst-choice '(swp swpb))))
      (when (code-has code '(ldm# stm#))
            (set! inst-choice (append inst-choice '(ldm# stm#))))
      (when (code-has code '(tst cmp teq cmn tst# cmp# teq# cmn#))
            (set! inst-choice (append inst-choice '(tst cmp teq cmn
                                                    tst# cmp# teq# cmn#))))

      (define base-opcodes (vector opcodes 0))
      (set! inst-choice-name inst-choice)
      (when debug (pretty-display `(inst-choice ,inst-choice-name)))
      (set! inst-choice (map (lambda (x) (get-base-opcode-id x)) inst-choice))
      (set! opcode-pool (filter (lambda (x) (member (vector-ref x 0) inst-choice)) opcode-pool))
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
      
      (define type-reg-sp (hash-ref argtypes-info 'reg-sp))
      (define reg-sp-list (argtype-valid type-reg-sp))

      (define exclude (append reg-list context-reg-list reg-sp-list))
      
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
        (define offset (vector-ref (progstate-regs state-base) offset))

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
