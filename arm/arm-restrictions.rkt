#lang racket

(require racket/match
         rosette
         "../inst.rkt")

(provide (all-defined-out))

(struct compiled-pattern (mask bits text) #:transparent)
(struct arm-restrictions (default allow deny source) #:transparent)

(define arm-u32-mask #xffffffff)

(define (compile-arm-pattern pattern)
  (unless (and (string? pattern) (= (string-length pattern) 32))
    (raise-user-error 'compile-arm-pattern
                      "expected a 32-character 0/1/x pattern, got ~s"
                      pattern))
  (define-values (mask bits)
    (for/fold ([mask 0] [bits 0])
              ([ch (in-string pattern)]
               [bit (in-range 31 -1 -1)])
      (define value (arithmetic-shift 1 bit))
      (case ch
        [(#\0) (values (bitwise-ior mask value) bits)]
        [(#\1) (values (bitwise-ior mask value)
                       (bitwise-ior bits value))]
        [(#\x #\X) (values mask bits)]
        [else
         (raise-user-error 'compile-arm-pattern
                           "expected only 0, 1, or x in pattern ~s"
                           pattern)])))
  (compiled-pattern mask bits pattern))

(define (load-arm-restrictions file)
  (define data
    (call-with-input-file file
      (lambda (in)
        (define first-form (read in))
        (define second-form (read in))
        (unless (eof-object? second-form)
          (raise-user-error 'load-arm-restrictions
                            "expected exactly one restriction datum in ~a"
                            file))
        first-form)))
  (unless (list? data)
    (raise-user-error 'load-arm-restrictions
                      "expected a list of restriction forms in ~a"
                      file))
  (define default 'allow)
  (define allow (list))
  (define deny (list))
  (for ([form data])
    (match form
      [`(default ,mode)
       (unless (member mode '(allow deny))
         (raise-user-error 'load-arm-restrictions
                           "default must be allow or deny, got ~s"
                           mode))
       (set! default mode)]
      [`(allow ,pattern)
       (set! allow (cons (compile-arm-pattern pattern) allow))]
      [`(deny ,pattern)
       (set! deny (cons (compile-arm-pattern pattern) deny))]
      [_
       (raise-user-error 'load-arm-restrictions
                         "unknown restriction form ~s"
                         form)]))
  (arm-restrictions default (reverse allow) (reverse deny) file))

(define (pattern-match? pattern word)
  (= (bitwise-and word (compiled-pattern-mask pattern))
     (compiled-pattern-bits pattern)))

(define (any-pattern-match? patterns word)
  (cond
    [(empty? patterns) #f]
    [else (or (pattern-match? (car patterns) word)
              (any-pattern-match? (cdr patterns) word))]))

(define (arm-word-allowed? restrictions word)
  (cond
    [(not restrictions) #t]
    [(not word) #f]
    [else
     (define base-allowed?
       (if (equal? (arm-restrictions-default restrictions) 'allow)
           #t
           (any-pattern-match? (arm-restrictions-allow restrictions) word)))
     (and base-allowed?
          (not (any-pattern-match? (arm-restrictions-deny restrictions) word)))]))

(define (sym-member? x xs)
  (cond
    [(empty? xs) #f]
    [else (or (equal? x (car xs)) (sym-member? x (cdr xs)))]))

(define (word . parts)
  (and (for/and ([part parts]) (not (equal? part #f)))
       (apply bitwise-ior parts)))

(define (lshift value amount)
  (if (term? value)
      (<< value amount)
      (arithmetic-shift value amount)))

(define (rshift value amount)
  (if (term? value)
      (>>> value amount)
      (arithmetic-shift value (- amount))))

(define (bits value shift)
  (and (not (equal? value #f)) (lshift value shift)))

(define (u32 value) (bitwise-and value arm-u32-mask))

(define (shl32 value amount)
  (u32 (lshift value amount)))

(define (ushr32 value amount)
  (>>> (u32 value) amount))

(define (ror32 value amount)
  (define v (u32 value))
  (if (= amount 0)
      v
      (u32 (bitwise-ior (ushr32 v amount)
                        (shl32 v (- 32 amount))))))

(define (rol32 value amount)
  (define v (u32 value))
  (if (= amount 0)
      v
      (u32 (bitwise-ior (shl32 v amount)
                        (ushr32 v (- 32 amount))))))

(define (encode-modified-immediate value)
  (define v (u32 value))
  (define symbolic? (term? v))
  (let loop ([rot 0])
    (cond
      [(= rot 16) (and symbolic? 0)]
      [else
       (define rotated (rol32 v (* 2 rot)))
       (define fits? (= (bitwise-and rotated #xffffff00) 0))
       (define encoded (bitwise-ior (arithmetic-shift rot 8)
	                                    (bitwise-and rotated #xff)))
	       (if fits? encoded (loop (add1 rot)))])))

(define (map-reg machine reg)
  (define reg-map (send machine get-restriction-reg-map))
  (cond
    [(not reg-map) reg]
    [(number? reg)
     (if (and (>= reg 0) (< reg (vector-length reg-map)))
         (vector-ref reg-map reg)
         reg)]
    [else (vector-ref reg-map reg)]))

(define (reg4 machine reg)
  (define mapped (map-reg machine reg))
  (cond
    [(term? mapped) mapped]
    [(number? mapped) (and (>= mapped 0) (< mapped 16) mapped)]
    [else mapped]))

(define (opcode-group machine group)
  (vector-ref (get-field opcodes machine) group))

(define (base-opcode-name machine op-id)
  (vector-ref (opcode-group machine 0) op-id))

(define (cond-opcode-name machine cond-id)
  (if (>= cond-id 0)
      (vector-ref (opcode-group machine 1) cond-id)
      '||))

(define (shf-opcode-name machine shf-id)
  (if (>= shf-id 0)
      (vector-ref (opcode-group machine 2) shf-id)
      '||))

(define (imm12 value)
  (cond
    [(term? value) (bitwise-and value #xfff)]
    [(number? value) (and (>= value 0) (< value 4096) value)]
    [else (bitwise-and value #xfff)]))

(define (imm16 value)
  (cond
    [(term? value) (bitwise-and value #xffff)]
    [(number? value) (and (>= value 0) (< value 65536) value)]
    [else (bitwise-and value #xffff)]))

(define (cond-symbol->code cond-name)
  (cond
    [(equal? cond-name 'eq) 0]
    [(equal? cond-name 'ne) 1]
    [(equal? cond-name 'cs) 2]
    [(equal? cond-name 'cc) 3]
    [(equal? cond-name 'mi) 4]
    [(equal? cond-name 'pl) 5]
    [(equal? cond-name 'vs) 6]
    [(equal? cond-name 'vc) 7]
    [(equal? cond-name 'hi) 8]
    [(equal? cond-name 'ls) 9]
    [(equal? cond-name 'ge) 10]
    [(equal? cond-name 'lt) 11]
    [(equal? cond-name 'gt) 12]
    [(equal? cond-name 'le) 13]
    [(equal? cond-name 'al) 14]
    [else 14]))

(define (arm-cond-code machine cond-id)
  (cond
    [(equal? cond-id -1) 14]
    [(term? cond-id)
     (define conds (opcode-group machine 1))
     (let loop ([id 0])
       (if (= id (vector-length conds))
           14
           (if (= cond-id id)
               (cond-symbol->code (vector-ref conds id))
               (loop (add1 id)))))]
    [else (cond-symbol->code (cond-opcode-name machine cond-id))]))

(define (shift-type shf-name)
  (cond
    [(sym-member? shf-name '(lsl lsl#)) 0]
    [(sym-member? shf-name '(lsr lsr#)) 1]
    [(sym-member? shf-name '(asr asr#)) 2]
    [(sym-member? shf-name '(ror ror#)) 3]
    [else 0]))

(define (shift-immediate-field shf-name amount)
  (define type (shift-type shf-name))
  (define imm5
    (cond
      [(term? amount) (bitwise-and amount #x1f)]
      [(number? amount)
       (cond
         [(and (= amount 32) (sym-member? shf-name '(lsr# asr#))) 0]
         [(and (>= amount 0) (< amount 32)) amount]
         [else #f])]
      [else (bitwise-and amount #x1f)]))
  (and imm5 (word (bits imm5 7) (bits type 5))))

(define (operand2-reg machine args rm-index)
  (reg4 machine (vector-ref args rm-index)))

(define (operand2-with-shift-name machine shf-name args rm-index shift-index)
  (define rm (reg4 machine (vector-ref args rm-index)))
  (cond
    [(equal? shf-name '||)
     rm]
    [(sym-member? shf-name '(lsl lsr asr ror))
     (define rs (reg4 machine (vector-ref args shift-index)))
     (word (bits rs 8) (bits (shift-type shf-name) 5) (bits 1 4) rm)]
    [(sym-member? shf-name '(lsl# lsr# asr# ror#))
     (word (shift-immediate-field shf-name (vector-ref args shift-index)) rm)]
    [else #f]))

(define (operand2-with-optional-shift machine shf-id args rm-index shift-index)
  (cond
    [(or (equal? shf-id #f) (equal? shf-id -1))
     (operand2-with-shift-name machine '|| args rm-index shift-index)]
    [(term? shf-id)
     (define shfs (opcode-group machine 2))
     (let loop ([id 0])
       (if (= id (vector-length shfs))
           #f
           (if (= shf-id id)
               (operand2-with-shift-name machine (vector-ref shfs id) args rm-index shift-index)
               (loop (add1 id)))))]
    [else
     (operand2-with-shift-name machine (shf-opcode-name machine shf-id)
                               args rm-index shift-index)]))

(define (dp-opcode op-name)
  (cond
    [(sym-member? op-name '(and and# ands ands#)) 0]
    [(sym-member? op-name '(eor eor# eors eors#)) 1]
    [(sym-member? op-name '(sub sub# subs subs#)) 2]
    [(sym-member? op-name '(rsb rsb# rsbs rsbs#)) 3]
    [(sym-member? op-name '(add add# adds adds#)) 4]
    [(sym-member? op-name '(adc adc# adcs adcs#)) 5]
    [(sym-member? op-name '(sbc sbc# sbcs sbcs#)) 6]
    [(sym-member? op-name '(rsc rsc# rscs rscs#)) 7]
    [(sym-member? op-name '(tst tst#)) 8]
    [(sym-member? op-name '(teq teq#)) 9]
    [(sym-member? op-name '(cmp cmp#)) 10]
    [(sym-member? op-name '(cmn cmn#)) 11]
    [(sym-member? op-name '(orr orr# orrs orrs# orn orn#)) 12]
    [(sym-member? op-name '(mov mov# movs movs# lsl lsl# lsr lsr# asr asr# ror ror#)) 13]
    [(sym-member? op-name '(bic bic# bics bics#)) 14]
    [(sym-member? op-name '(mvn mvn# mvns mvns#)) 15]
    [else #f]))

(define (dp-s-bit op-name)
  (if (sym-member? op-name
                   '(adds adcs subs rsbs sbcs rscs ands orrs eors bics
                     adds# adcs# subs# rsbs# sbcs# rscs# ands# orrs# eors# bics#
                     movs mvns movs# mvns#
                     tst teq cmp cmn tst# teq# cmp# cmn#))
      1
      0))

(define (dp-word cond-code opcode s-bit rn rd operand2 #:immediate? [immediate? #f])
  (word (bits cond-code 28)
        (if immediate? #x02000000 0)
        (bits opcode 21)
        (bits s-bit 20)
        (bits rn 16)
        (bits rd 12)
        operand2))

(define (encode-dp-reg machine cond-code op-name shf-id args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rn (reg4 machine (vector-ref args 1)))
  (define operand2 (operand2-with-optional-shift machine shf-id args 2 3))
  (dp-word cond-code (dp-opcode op-name) (dp-s-bit op-name) rn rd operand2))

(define (encode-dp-imm machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rn (reg4 machine (vector-ref args 1)))
  (define operand2 (encode-modified-immediate (vector-ref args 2)))
  (and operand2
       (dp-word cond-code (dp-opcode op-name) (dp-s-bit op-name) rn rd operand2
                #:immediate? #t)))

(define (encode-mov-reg machine cond-code op-name shf-id args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define operand2 (operand2-with-optional-shift machine shf-id args 1 2))
  (dp-word cond-code (dp-opcode op-name) (dp-s-bit op-name) 0 rd operand2))

(define (encode-mov-imm machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define operand2 (encode-modified-immediate (vector-ref args 1)))
  (and operand2
       (dp-word cond-code (dp-opcode op-name) (dp-s-bit op-name) 0 rd operand2
                #:immediate? #t)))

(define (encode-cmp-reg machine cond-code op-name shf-id args)
  (define rn (reg4 machine (vector-ref args 0)))
  (define operand2 (operand2-with-optional-shift machine shf-id args 1 2))
  (dp-word cond-code (dp-opcode op-name) 1 rn 0 operand2))

(define (encode-cmp-imm machine cond-code op-name args)
  (define rn (reg4 machine (vector-ref args 0)))
  (define operand2 (encode-modified-immediate (vector-ref args 1)))
  (and operand2
       (dp-word cond-code (dp-opcode op-name) 1 rn 0 operand2
                #:immediate? #t)))

(define (encode-shift machine cond-code op-name args #:register? register?)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rm (reg4 machine (vector-ref args 1)))
  (define operand2
    (if register?
        (let ([rs (reg4 machine (vector-ref args 2))])
          (word (bits rs 8) (bits (shift-type op-name) 5) (bits 1 4) rm))
        (word (shift-immediate-field op-name (vector-ref args 2)) rm)))
  (dp-word cond-code 13 0 0 rd operand2))

(define (encode-movw/movt machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define imm (imm16 (vector-ref args 1)))
  (and imm
       (word (bits cond-code 28)
             (if (equal? op-name 'movt#) #x03400000 #x03000000)
             (bits (bitwise-and (rshift imm 12) #xf) 16)
             (bits rd 12)
             (bitwise-and imm #xfff))))

(define (encode-mul machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rm (reg4 machine (vector-ref args 1)))
  (define rs (reg4 machine (vector-ref args 2)))
  (word (bits cond-code 28)
        #x00000090
        (if (equal? op-name 'muls) #x00100000 0)
        (bits rd 16)
        (bits rs 8)
        rm))

(define (encode-mla/mls machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rm (reg4 machine (vector-ref args 1)))
  (define rs (reg4 machine (vector-ref args 2)))
  (define ra (reg4 machine (vector-ref args 3)))
  (word (bits cond-code 28)
        (cond
          [(equal? op-name 'mls) #x00600090]
          [(equal? op-name 'mlas) #x00300090]
          [else #x00200090])
        (bits rd 16)
        (bits ra 12)
        (bits rs 8)
        rm))

(define (encode-long-mul machine cond-code op-name args)
  (define rdlo (reg4 machine (vector-ref args 0)))
  (define rdhi (reg4 machine (vector-ref args 1)))
  (define rm (reg4 machine (vector-ref args 2)))
  (define rs (reg4 machine (vector-ref args 3)))
  (word (bits cond-code 28)
        (cond
          [(equal? op-name 'umull) #x00800090]
          [(equal? op-name 'umulls) #x00900090]
          [(equal? op-name 'smlal) #x00e00090]
          [(equal? op-name 'smlals) #x00f00090]
          [(equal? op-name 'umlal) #x00a00090]
          [(equal? op-name 'umlals) #x00b00090]
          [(equal? op-name 'smulls) #x00d00090]
          [else #x00c00090])
        (bits rdhi 16)
        (bits rdlo 12)
        (bits rs 8)
        rm))

(define (encode-smmul/smmla machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rn (reg4 machine (vector-ref args 1)))
  (define rm (reg4 machine (vector-ref args 2)))
  (define ra
    (if (equal? op-name 'smmul)
        15
        (reg4 machine (vector-ref args 3))))
  (word (bits cond-code 28)
        (if (equal? op-name 'smmls) #x075000d0 #x07500010)
        (bits rd 16)
        (bits ra 12)
        (bits rm 8)
        rn))

(define (encode-div machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rn (reg4 machine (vector-ref args 1)))
  (define rm (reg4 machine (vector-ref args 2)))
  (word (bits cond-code 28)
        (if (equal? op-name 'udiv) #x0730f010 #x0710f010)
        (bits rd 16)
        (bits rm 8)
        rn))

(define (encode-uxt machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (cond
    [(equal? op-name 'uxtah)
     (define rn (reg4 machine (vector-ref args 1)))
     (define rm (reg4 machine (vector-ref args 2)))
     (word (bits cond-code 28) #x06f00070 (bits rn 16) (bits rd 12) rm)]
    [else
     (define rm (reg4 machine (vector-ref args 1)))
     (word (bits cond-code 28)
           (if (equal? op-name 'uxtb) #x06ef0070 #x06ff0070)
           (bits rd 12)
           rm)]))

(define (encode-bitfield machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (cond
    [(sym-member? op-name '(bfi sbfx ubfx))
     (define rn (reg4 machine (vector-ref args 1)))
     (define lsb (vector-ref args 2))
     (define width (vector-ref args 3))
     (define top (if (equal? op-name 'bfi) (+ lsb width -1) (sub1 width)))
     (word (bits cond-code 28)
           (cond
             [(equal? op-name 'bfi) #x07c00010]
             [(equal? op-name 'sbfx) #x07a00050]
             [else #x07e00050])
           (bits top 16)
           (bits rd 12)
           (bits lsb 7)
           rn)]
    [else
     (define lsb (vector-ref args 1))
     (define width (vector-ref args 2))
     (define msb (+ lsb width -1))
     (word (bits cond-code 28)
           #x07c00010
           (bits msb 16)
           (bits rd 12)
           (bits lsb 7)
           15)]))

(define (encode-reverse machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rm (reg4 machine (vector-ref args 1)))
  (word (bits cond-code 28)
        (cond
          [(equal? op-name 'rev) #x06bf0f30]
          [(equal? op-name 'rev16) #x06bf0fb0]
          [(equal? op-name 'revsh) #x06ff0fb0]
          [else #x06ff0f30])
        (bits rd 12)
        rm))

(define (encode-clz machine cond-code args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rm (reg4 machine (vector-ref args 1)))
  (word (bits cond-code 28) #x016f0f10 (bits rd 12) rm))

(define (load-store-byte? op-name)
  (sym-member? op-name '(ldrb ldrb# strb strb#)))

(define (load-store-load? op-name)
  (sym-member? op-name '(ldr ldr# ldrb ldrb# ldrh ldrh# ldrsb ldrsb# ldrsh ldrsh#)))

(define (word-transfer? op-name)
  (sym-member? op-name '(ldr ldr# str str# ldrb ldrb# strb strb#)))

(define (encode-load-store machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rn (reg4 machine (vector-ref args 1)))
  (cond
    [(sym-member? op-name '(ldr# str# ldrb# strb#))
     (define raw-offset (vector-ref args 2))
     (define byte-offset
       (if (sym-member? op-name '(ldr# str#))
           (* 4 raw-offset)
           raw-offset))
     (define positive? (or (not (number? byte-offset)) (>= byte-offset 0)))
     (define offset (imm12 (if (number? byte-offset) (abs byte-offset) byte-offset)))
     (and offset
          (word (bits cond-code 28)
                #x05000000
                (if (load-store-load? op-name) #x00100000 0)
                (if (load-store-byte? op-name) #x00400000 0)
                (if positive? #x00800000 0)
                (bits rn 16)
                (bits rd 12)
                offset))]
    [(sym-member? op-name '(ldr str ldrb strb))
     (define rm (reg4 machine (vector-ref args 2)))
     (word (bits cond-code 28)
           #x07000000
           (if (load-store-load? op-name) #x00100000 0)
           (if (load-store-byte? op-name) #x00400000 0)
           #x00800000
           (bits rn 16)
           (bits rd 12)
           rm)]
    [else #f]))

(define (halfword-sh op-name)
  (cond
    [(sym-member? op-name '(strh strh# ldrh ldrh#)) 1]
    [(sym-member? op-name '(ldrsb ldrsb#)) 2]
    [(sym-member? op-name '(ldrsh ldrsh#)) 3]
    [else #f]))

(define (encode-halfword-transfer machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rn (reg4 machine (vector-ref args 1)))
  (define sh (halfword-sh op-name))
  (cond
    [(sym-member? op-name '(ldrh# strh# ldrsb# ldrsh#))
     (define raw-offset (vector-ref args 2))
     (define positive? (or (not (number? raw-offset)) (>= raw-offset 0)))
     (define offset (if (number? raw-offset) (abs raw-offset) raw-offset))
     (define imm8 (and (or (term? offset) (and (number? offset) (< offset 256))) offset))
     (and sh imm8
          (word (bits cond-code 28)
                #x01000090
                #x00400000
                (if positive? #x00800000 0)
                (if (load-store-load? op-name) #x00100000 0)
                (bits rn 16)
                (bits rd 12)
                (bits (bitwise-and (rshift imm8 4) #xf) 8)
                (bits sh 5)
                (bitwise-and imm8 #xf)))]
    [(sym-member? op-name '(ldrh strh ldrsb ldrsh))
     (define rm (reg4 machine (vector-ref args 2)))
     (and sh
          (word (bits cond-code 28)
                #x01000090
                #x00800000
                (if (load-store-load? op-name) #x00100000 0)
                (bits rn 16)
                (bits rd 12)
                (bits sh 5)
                rm))]
    [else #f]))

(define (encode-swp machine cond-code op-name args)
  (define rd (reg4 machine (vector-ref args 0)))
  (define rm (reg4 machine (vector-ref args 1)))
  (define rn (reg4 machine (vector-ref args 2)))
  (word (bits cond-code 28)
        #x01000090
        (if (equal? op-name 'swpb) #x00400000 0)
        (bits rn 16)
        (bits rd 12)
        rm))

(define (encode-block-transfer machine cond-code op-name args)
  (define rn (reg4 machine (vector-ref args 0)))
  (define regmask (bitwise-and (vector-ref args 1) #xffff))
  (word (bits cond-code 28)
        #x08000000
        #x00800000
        (if (equal? op-name 'ldm#) #x00100000 0)
        (bits rn 16)
        regmask))

(define (arm-inst->word-by-name machine op-name cond-code shf-id args)
  (cond
    [(equal? op-name 'nop) (word (bits cond-code 28) #x0320f000)]
    [(sym-member? op-name '(add adc sub rsb sbc rsc and orr eor bic orn
                            adds adcs subs rsbs sbcs rscs ands orrs eors bics))
     (encode-dp-reg machine cond-code op-name shf-id args)]
    [(sym-member? op-name '(add# adc# sub# rsb# sbc# rsc# and# orr# eor# bic# orn#
                            adds# adcs# subs# rsbs# sbcs# rscs# ands# orrs# eors# bics#))
     (encode-dp-imm machine cond-code op-name args)]
    [(sym-member? op-name '(mov mvn movs mvns))
     (encode-mov-reg machine cond-code op-name shf-id args)]
    [(sym-member? op-name '(mov# mvn# movs# mvns#))
     (encode-mov-imm machine cond-code op-name args)]
    [(sym-member? op-name '(cmp tst teq cmn))
     (encode-cmp-reg machine cond-code op-name shf-id args)]
    [(sym-member? op-name '(cmp# tst# teq# cmn#))
     (encode-cmp-imm machine cond-code op-name args)]
    [(sym-member? op-name '(lsl lsr asr ror))
     (encode-shift machine cond-code op-name args #:register? #t)]
    [(sym-member? op-name '(lsl# lsr# asr# ror#))
     (encode-shift machine cond-code op-name args #:register? #f)]
    [(sym-member? op-name '(movw# movt#))
     (encode-movw/movt machine cond-code op-name args)]
    [(sym-member? op-name '(mul muls)) (encode-mul machine cond-code op-name args)]
    [(sym-member? op-name '(mla mlas mls)) (encode-mla/mls machine cond-code op-name args)]
    [(sym-member? op-name '(smull umull smulls umulls smlal umlal smlals umlals))
     (encode-long-mul machine cond-code op-name args)]
    [(sym-member? op-name '(smmul smmla smmls)) (encode-smmul/smmla machine cond-code op-name args)]
    [(sym-member? op-name '(sdiv udiv)) (encode-div machine cond-code op-name args)]
    [(sym-member? op-name '(uxtah uxth uxtb)) (encode-uxt machine cond-code op-name args)]
    [(sym-member? op-name '(bfi bfc sbfx ubfx)) (encode-bitfield machine cond-code op-name args)]
    [(sym-member? op-name '(rev rev16 revsh rbit)) (encode-reverse machine cond-code op-name args)]
    [(equal? op-name 'clz) (encode-clz machine cond-code args)]
    [(word-transfer? op-name) (encode-load-store machine cond-code op-name args)]
    [(sym-member? op-name '(ldrh ldrh# strh strh# ldrsb ldrsb# ldrsh ldrsh#))
     (encode-halfword-transfer machine cond-code op-name args)]
    [(sym-member? op-name '(swp swpb)) (encode-swp machine cond-code op-name args)]
    [(sym-member? op-name '(ldm# stm#)) (encode-block-transfer machine cond-code op-name args)]
    [else
     (raise-user-error 'arm-inst->word
                       "no canonical ARM32 encoder for opcode ~s"
                       op-name)]))

(define (arm-inst->word machine my-inst)
  (define ops-vec (inst-op my-inst))
  (define args (inst-args my-inst))
  (define op-id (vector-ref ops-vec 0))
  (define cond-id (vector-ref ops-vec 1))
  (define shf-id (vector-ref ops-vec 2))
  (define cond-code (arm-cond-code machine cond-id))
  (cond
    [(term? op-id)
     (define base-opcodes (opcode-group machine 0))
     (let loop ([id 0])
       (if (= id (vector-length base-opcodes))
           #f
           (if (= op-id id)
               (arm-inst->word-by-name machine (vector-ref base-opcodes id)
                                       cond-code shf-id args)
               (loop (add1 id)))))]
    [else
     (arm-inst->word-by-name machine (base-opcode-name machine op-id)
                             cond-code shf-id args)]))

(define (arm-inst-allowed? restrictions machine my-inst)
  (arm-word-allowed? restrictions (arm-inst->word machine my-inst)))

(define (arm-program-allowed? restrictions machine code)
  (for/and ([my-inst code])
    (arm-inst-allowed? restrictions machine my-inst)))
