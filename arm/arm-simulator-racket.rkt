#lang racket

(require "../simulator.rkt" "../ops-racket.rkt" 
         "../inst.rkt"
         "../machine.rkt" "arm-machine.rkt")
(provide arm-simulator-racket%)

(define arm-simulator-racket%
  (class simulator%
    (super-new)
    (init-field machine)
    (override interpret performance-cost get-constructor is-valid?)

    (define (get-constructor) arm-simulator-racket%)

    (define (is-valid? code)
      (send machine program-allowed? code))
        
    (define bit (get-field bitwidth machine))

    (define opcodes (get-field opcodes machine))
    (define base-opcodes (vector-ref opcodes 0))
    (define cond-opcodes (vector-ref opcodes 1))
    (define shf-opcodes (vector-ref opcodes 2))
    (define ninsts (vector-length base-opcodes))

    (define (shl a b) (<< a b bit))
    (define (ushr a b) (>>> a b bit))
    (define (ror a b) (bitwise-ior (>>> a b bit) (<< a (- bit b) bit)))
    (define-syntax-rule (finitize-bit x) (finitize x bit))

    (define byte0 0)
    (define byte1 (quotient bit 4))
    (define byte2 (* 2 byte1))
    (define byte3 (* 3 byte1))
    (define byte4 bit)
    (define byte-mask (sub1 (arithmetic-shift 1 byte1)))
    (define low-mask (sub1 (shl 1 byte2)))
    (define high-mask (shl low-mask byte2))
    (define mask (sub1 (arithmetic-shift 1 bit)))

    ;; helper functions
    (define-syntax-rule (bool->num b) (if b 1 0))

    (define-syntax-rule (bvop op)     
      (lambda (x y) (finitize-bit (op x y))))

    (define-syntax-rule (bvuop op)     
      (lambda (x) (finitize-bit (op x))))

    (define-syntax-rule (bvcmp op) 
      (lambda (x y) (bool->num (op x y))))

    (define-syntax-rule (bvucmp op)   
      (lambda (x y) 
        (bool->num (if (equal? (< x 0) (< y 0)) (op x y) (op y x)))))

    (define-syntax-rule (bvshift op)
      (lambda (x y)
        (finitize-bit (op x (bitwise-and #xff y)))))

    (define-syntax-rule (bvshift# op)
      (lambda (x y)
	;;(pretty-display `(bvshift assert ,y))
	(assert (and (>= y 0) (<= y bit)))
        (finitize-bit (op x y))))

    (define-syntax-rule (bvbit op)
      (lambda (a b)
        (if (and (>= b 0) (< b bit))
            (finitize-bit (op a (shl 1 b)))
            a)))

    (define bvadd (bvop +))
    (define bvsub (bvop -))
    (define bvrsub (bvop (lambda (x y) (- y x))))

    (define bvnot (lambda (x) (finitize-bit (bitwise-not x))))
    (define bvand (bvop bitwise-and))
    (define bvor  (bvop bitwise-ior))
    (define bvxor (bvop bitwise-xor))
    (define bvandn (lambda (x y) (finitize-bit (bitwise-and x (bitwise-not y)))))
    (define bviorn  (lambda (x y) (finitize-bit (bitwise-ior x (bitwise-not y)))))

    (define bvrev (bvuop rev))
    (define bvrev16 (bvuop rev16))
    (define bvrevsh (bvuop revsh))
    (define bvrbit (bvuop rbit))

    (define bvshl  (bvshift shl))
    (define bvshr  (bvshift >>))
    (define bvushr (bvshift ushr))
    (define bvror  (bvshift ror))

    (define bvshl#  (bvshift# shl))
    (define bvshr#  (bvshift# >>))
    (define bvushr# (bvshift# ushr))
    (define bvror#  (bvshift# ror))

    (define uxtah (bvop (lambda (x y) (+ x (bitwise-and y low-mask)))))
    (define uxth (lambda (x) (finitize-bit (bitwise-and x low-mask))))
    (define uxtb (lambda (x) (finitize-bit (bitwise-and x byte-mask))))

    (define bvmul (bvop *))
    (define bvmla (lambda (a b c) (finitize-bit (+ c (* a b)))))
    (define bvmls (lambda (a b c) (finitize-bit (- c (* a b)))))
    (define bvsmmla (lambda (a b c) (finitize-bit (+ c (bvsmmul a b)))))
    (define bvsmmls (lambda (a b c) (finitize-bit (- c (bvsmmul a b)))))

    (define (bvsmmul x y) (smmul x y bit))
    (define (bvummul x y) (ummul x y bit))
    (define bvsdiv (bvop quotient))
    (define (bvudiv n d)
      (if (< d 0)
          (if (< n d) 1 0)
          (let* ([q (shl (quotient (ushr n 2) d) 2)]
                 [r (- n (* q d))])
            (finitize-bit (if (or (> r d) (< r 0)) q (add1 q))))))
      

    (define (movlo to c)
      (finitize-bit (bitwise-ior (bitwise-and to high-mask) c)))
    
    (define (movhi to c)
      (finitize-bit (bitwise-ior (bitwise-and to low-mask) (shl c byte2))))

    (define (setbit d a width shift)
      (assert (and (>= shift 0) (< shift bit)))
      (assert (and (> width 0) (<= (+ width shift) bit)))
      (let* ([mask (sub1 (shl 1 width))]
             [keep (bitwise-and d (bitwise-not (shl mask shift)))]
             [insert (bvshl# (bitwise-and a mask) shift)])
        (finitize-bit (bitwise-ior keep insert))))

    (define (clrbit d width shift)
      (assert (and (>= shift 0) (< shift bit)))
      (assert (and (> width 0) (<= (+ width shift) bit)))
      (let* ([keep (bitwise-not (shl (sub1 (shl 1 width)) shift))])
        (finitize-bit (bitwise-and keep d))))

    (define (ext d a width shift)
      (assert (and (>= shift 0) (< shift bit)))
      (assert (and (> width 0) (<= (+ width shift) bit)))
      (finitize-bit (bitwise-and (>> a shift) (sub1 (shl 1 width)))))

    (define (sext d a width shift)
      (assert (and (>= shift 0) (< shift bit)))
      (assert (and (> width 0) (<= (+ width shift) bit)))
      (let ([keep (bitwise-and (>> a shift) (sub1 (shl 1 width)))])
        (bitwise-ior
         (if (= (bitwise-bit-field keep (sub1 width) width) 1)
             (shl -1 width)
             0)
         (finitize-bit keep))))

    (define (clz x)
      (let ([mask (shl 1 (sub1 bit))]
            [count 0]
            [still #t])
        (for ([i bit])
             (when still
                   (let ([res (bitwise-and x mask)])
                     (set! x (shl x 1))
                     (if (= res 0)
                         (set! count (add1 count))
                         (set! still #f)))))
        count))

    (define (rev a)
      (bitwise-ior 
       (shl (bitwise-bit-field a byte0 byte1) byte3)
       (shl (bitwise-bit-field a byte1 byte2) byte2)
       (shl (bitwise-bit-field a byte2 byte3) byte1)
       (bitwise-bit-field a byte3 byte4)))

    (define (rev16 a)
      (bitwise-ior 
       (shl (bitwise-bit-field a byte2 byte3) byte3)
       (shl (bitwise-bit-field a byte3 byte4) byte2)
       (shl (bitwise-bit-field a byte0 byte1) byte1)
       (bitwise-bit-field a byte1 byte2)))

    (define (revsh a)
      (bitwise-ior 
       (if (= (bitwise-bit-field a (sub1 byte1) byte1) 1) high-mask 0)
       (shl (bitwise-bit-field a byte0 byte1) byte1)
       (bitwise-bit-field a byte1 byte2)))

    (define (rbit a)
      (let ([res 0])
        (for ([i bit])
             (set! res (bitwise-ior (shl res 1) (bitwise-and a 1)))
             (set! a (>> a 1)))
        res))

    ;; Packed NZCV flags in the z slot.
    (define-syntax-rule (flag-n flags) (bitwise-bit-field flags 3 4))
    (define-syntax-rule (flag-z flags) (bitwise-bit-field flags 2 3))
    (define-syntax-rule (flag-c flags) (bitwise-bit-field flags 1 2))
    (define-syntax-rule (flag-v flags) (bitwise-bit-field flags 0 1))
    (define (pack-flags n z c v)
      (bitwise-ior (shl (bool->num n) 3)
                   (shl (bool->num z) 2)
                   (shl (bool->num c) 1)
                   (bool->num v)))
    (define (same-cv-flags result old-flags)
      (pack-flags (< (finitize-bit result) 0)
                  (= (finitize-bit result) 0)
                  (= (flag-c old-flags) 1)
                  (= (flag-v old-flags) 1)))
    (define (same-cv-flags64 lo hi old-flags)
      (pack-flags (< (finitize-bit hi) 0)
                  (and (= (finitize-bit lo) 0) (= (finitize-bit hi) 0))
                  (= (flag-c old-flags) 1)
                  (= (flag-v old-flags) 1)))
    (define (logical-flags result carry old-flags)
      (pack-flags (< (finitize-bit result) 0)
                  (= (finitize-bit result) 0)
                  carry
                  (= (flag-v old-flags) 1)))
    (define (u32 x) (bitwise-and x mask))
    (define signed-min (- (arithmetic-shift 1 (sub1 bit))))
    (define signed-max (sub1 (arithmetic-shift 1 (sub1 bit))))
    (define unsigned-limit (arithmetic-shift 1 bit))

    (define (add-carry-out x y carry)
      (>= (+ (u32 x) (u32 y) (bool->num carry)) unsigned-limit))
    (define (sub-carry-out x y borrow)
      (>= (u32 x) (+ (u32 y) (bool->num borrow))))
    (define (signed-overflow? raw)
      (or (< raw signed-min) (> raw signed-max)))
    (define (add-flags x y carry result)
      (pack-flags (< result 0)
                  (= result 0)
                  (add-carry-out x y carry)
                  (signed-overflow? (+ x y (bool->num carry)))))
    (define (sub-flags x y borrow result)
      (pack-flags (< result 0)
                  (= result 0)
                  (sub-carry-out x y borrow)
                  (signed-overflow? (- x y (bool->num borrow)))))

    (define (condition-holds? cond-type flags)
      (define n (= (flag-n flags) 1))
      (define zf (= (flag-z flags) 1))
      (define c (= (flag-c flags) 1))
      (define v (= (flag-v flags) 1))
      (cond
       [(or (equal? cond-type -1) (equal? cond-type 14)) #t]
       [(equal? cond-type 0) zf]
       [(equal? cond-type 1) (not zf)]
       [(equal? cond-type 2) c]
       [(equal? cond-type 3) (not c)]
       [(equal? cond-type 4) n]
       [(equal? cond-type 5) (not n)]
       [(equal? cond-type 6) v]
       [(equal? cond-type 7) (not v)]
       [(equal? cond-type 8) (and c (not zf))]
       [(equal? cond-type 9) (or (not c) zf)]
       [(equal? cond-type 10) (equal? n v)]
       [(equal? cond-type 11) (not (equal? n v))]
       [(equal? cond-type 12) (and (not zf) (equal? n v))]
       [(equal? cond-type 13) (or zf (not (equal? n v)))]
       [else #f]))
    
    ;; Interpret a given program from a given state.
    ;; state: initial progstate
    (define (interpret program state [ref #f])
      (define opcode-pool (get-field opcode-pool machine))
      ;;(pretty-display `(interpret))
      (define regs (vector-copy (progstate-regs state)))
      (define memory #f)
      (define z (progstate-z state))

      (define (interpret-step step)
        (define ops-vec (inst-op step))
        (define args (inst-args step))
        
        (define op (vector-ref ops-vec 0))
        (define cond-type (vector-ref ops-vec 1))
        (define shfop (vector-ref ops-vec 2))
        (define op-name (vector-ref base-opcodes op))
        (define shfop-name (and (>= shfop 0) (vector-ref shf-opcodes shfop)))
        
        ;; (pretty-display `(interpret-step ,ops-vec))

        (define-syntax-rule (inst-eq a ...)
          (or (equal? a op-name) ...))
        (define-syntax-rule (shf-inst-eq a ...)
          (or (equal? a shfop-name) ...))

        (define-syntax-rule (args-ref args i) (vector-ref args i))

        (define (exec)
          (define old-carry (= (flag-c z) 1))

          (define (shift-carry value amount direction)
            (cond
             [(not (number? amount)) old-carry]
             [(= amount 0) old-carry]
             [(equal? direction 'left)
              (if (and (>= amount 1) (<= amount bit))
                  (= (bitwise-bit-field value (- bit amount) (add1 (- bit amount))) 1)
                  #f)]
             [(equal? direction 'right)
              (if (and (>= amount 1) (<= amount bit))
                  (= (bitwise-bit-field value (sub1 amount) amount) 1)
                  #f)]
             [(equal? direction 'asr)
              (if (and (>= amount 1) (< amount bit))
                  (= (bitwise-bit-field value (sub1 amount) amount) 1)
                  (< (finitize-bit value) 0))]
             [else old-carry]))

          (define (ror-carry value amount)
            (if (or (not (number? amount)) (= amount 0))
                old-carry
                (< (finitize-bit (ror value amount)) 0)))

          (define (shift-result-and-carry value shf-name amount register-shift?)
            (define amt (if register-shift? (bitwise-and amount #xff) amount))
            (cond
             [(or (equal? shf-name #f) (equal? shf-name -1) (equal? shf-name '||))
              (values value old-carry)]
             [(equal? shf-name 'lsl)
              (values (finitize-bit (shl value amt))
                      (shift-carry value amt 'left))]
             [(equal? shf-name 'lsl#)
              (values (finitize-bit (shl value amt))
                      (shift-carry value amt 'left))]
             [(equal? shf-name 'lsr)
              (values (finitize-bit (ushr value amt))
                      (shift-carry value amt 'right))]
             [(equal? shf-name 'lsr#)
              (define real-amt (if (= amt 0) bit amt))
              (values (finitize-bit (ushr value real-amt))
                      (shift-carry value real-amt 'right))]
             [(equal? shf-name 'asr)
              (values (finitize-bit (>> value amt))
                      (shift-carry value amt 'asr))]
             [(equal? shf-name 'asr#)
              (define real-amt (if (= amt 0) bit amt))
              (values (finitize-bit (>> value real-amt))
                      (shift-carry value real-amt 'asr))]
             [(equal? shf-name 'ror)
              (define real-amt (if (number? amt) (modulo amt bit) (bitwise-and amt #x1f)))
              (values (finitize-bit (ror value real-amt))
                      (ror-carry value real-amt))]
             [(equal? shf-name 'ror#)
              (if (= amt 0)
                  (values (finitize-bit
                           (bitwise-ior
                            (if old-carry (arithmetic-shift 1 (sub1 bit)) 0)
                            (ushr value 1)))
                          (= (bitwise-bit-field value 0 1) 1))
                  (values (finitize-bit (ror value amt))
                          (ror-carry value amt)))]
             [else
              (assert #f (format "undefine optional shift: ~a" shfop))
              (values value old-carry)]))

          (define (opt-shift x)
            (define len (vector-length args))
            (define k (and (> len 0) (vector-ref args (sub1 len))))
            (define shf-name (and (>= shfop 0) (vector-ref shf-opcodes shfop)))
            (define register-shift? (member shf-name '(lsr asr lsl ror)))
            (define amount
              (if register-shift?
                  (vector-ref regs k)
                  (if k k 0)))
            (shift-result-and-carry (vector-ref regs x) shf-name amount register-shift?))

          ;; sub add
          (define (rrr f [shf #f])
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define-values (reg-b-val sh-carry)
	      (if shf
		  (opt-shift b)
		  (values (vector-ref regs b) old-carry)))
            (define val (f (vector-ref regs a) reg-b-val))
            (vector-set! regs d val))

          (define (rrrr f)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define c (args-ref args 3))
            (define val (f (vector-ref regs a) (vector-ref regs b) (vector-ref regs c)))
            (vector-set! regs d val))

          (define (rrr-s f)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define val (f (vector-ref regs a) (vector-ref regs b)))
            (vector-set! regs d val)
            (set! z (same-cv-flags val z)))

          (define (rrrr-s f)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define c (args-ref args 3))
            (define val (f (vector-ref regs a) (vector-ref regs b) (vector-ref regs c)))
            (vector-set! regs d val)
            (set! z (same-cv-flags val z)))

          (define (ddrr f-lo f-hi [set-flags? #f])
            (define d-lo (args-ref args 0))
            (define d-hi (args-ref args 1))
            (assert (not (= d-lo d-hi)))
            (define a (args-ref args 2))
            (define b (args-ref args 3))
            (define val-lo (f-lo (vector-ref regs a) (vector-ref regs b)))
            (define val-hi (f-hi (vector-ref regs a) (vector-ref regs b)))
            (vector-set! regs d-lo val-lo)
            (vector-set! regs d-hi val-hi)
            (when set-flags? (set! z (same-cv-flags64 val-lo val-hi z))))

          ;; count leading zeros
          (define (rr f [shf #f])
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define-values (reg-a-val sh-carry)
	      (if shf
		  (opt-shift a)
		  (values (vector-ref regs a) old-carry)))
            (define val (f reg-a-val))
            (vector-set! regs d val))

          ;; mov
          (define (ri f)
            (define d (args-ref args 0))
            (define a (check-imm-mov (args-ref args 1)))
            (define val (f a))
            (vector-set! regs d val))

          ;; movhi movlo
          (define (r!i f)
            (define d (args-ref args 0))
            (define a (check-imm-mov (args-ref args 1)))
            (define val (f (vector-ref regs d) a))
            (vector-set! regs d val))

          ;; subi addi
          (define (rri f)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (check-imm (args-ref args 2)))
            (define val (f (vector-ref regs a) b))
            (vector-set! regs d val))

          ;; lsr
          (define (rrb f)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define val (f (vector-ref regs a) b))
            (vector-set! regs d val))

          ;; store
          (define (str reg-offset)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define index 
              (if reg-offset
                  (+ (vector-ref regs a) (vector-ref regs b))
                  (+ (vector-ref regs a) b)))
            (define val
              (cond
               [(inst-eq `strb `strb#) (bitwise-and (vector-ref regs d) #xff)]
               [(inst-eq `strh `strh#) (bitwise-and (vector-ref regs d) #xffff)]
               [else (vector-ref regs d)]))
            (unless memory
              (set! memory (send* (progstate-memory state) clone
                                 (and ref (progstate-memory ref)))))
            (send* memory store (finitize-bit index) val))

          ;; load
          (define (ldr reg-offset)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define index 
              (if reg-offset
                  (+ (vector-ref regs a) (vector-ref regs b))
                  (+ (vector-ref regs a) b)))
            (unless memory
              (set! memory (send* (progstate-memory state) clone
                                 (and ref (progstate-memory ref)))))
            (define raw-val (send* memory load (finitize-bit index)))
            (define val
              (cond
               [(inst-eq `ldrb `ldrb#) (bitwise-and raw-val #xff)]
               [(inst-eq `ldrh `ldrh#) (bitwise-and raw-val #xffff)]
               [(inst-eq `ldrsb `ldrsb#)
                (let ([byte (bitwise-and raw-val #xff)])
                  (if (>= byte #x80) (finitize-bit (bitwise-ior byte #xffffff00)) byte))]
               [(inst-eq `ldrsh `ldrsh#)
                (let ([half (bitwise-and raw-val #xffff)])
                  (if (>= half #x8000) (finitize-bit (bitwise-ior half #xffff0000)) half))]
               [else raw-val]))
            (vector-set! regs d val))

          (define (swp)
            (define d (args-ref args 0))
            (define m (args-ref args 1))
            (define n (args-ref args 2))
            (define index (vector-ref regs n))
            (unless memory
              (set! memory (send* (progstate-memory state) clone
                                 (and ref (progstate-memory ref)))))
            (define raw-val (send* memory load (finitize-bit index)))
            (define loaded (if (inst-eq `swpb) (bitwise-and raw-val #xff) raw-val))
            (define stored (if (inst-eq `swpb) (bitwise-and (vector-ref regs m) #xff) (vector-ref regs m)))
            (vector-set! regs d loaded)
            (send* memory store (finitize-bit index) stored))

          (define (block-transfer load?)
            (define n (args-ref args 0))
            (define mask (args-ref args 1))
            (define base (vector-ref regs n))
            (unless memory
              (set! memory (send* (progstate-memory state) clone
                                 (and ref (progstate-memory ref)))))
            (define offset 0)
            (for ([reg-id (in-range (min bit (vector-length regs)))])
              (when (= (bitwise-bit-field mask reg-id (add1 reg-id)) 1)
                (define addr (finitize-bit (+ base (* 4 offset))))
                (if load?
                    (vector-set! regs reg-id (send* memory load addr))
                    (send* memory store addr (vector-ref regs reg-id)))
                (set! offset (add1 offset)))))

          ;; setbit
          (define (rrbb f)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define width (args-ref args 3))
            (define shift (args-ref args 2))
            (define val (f (vector-ref regs d) (vector-ref regs a) width shift))
            (vector-set! regs d val))

          ;; clrbit
          (define (r!bb f)
            (define d (args-ref args 0))
            (define width (args-ref args 2))
            (define shift (args-ref args 1))
            (define val (f (vector-ref regs d) width shift))
            (vector-set! regs d val))

          (define (z=rr f)
            (define a (args-ref args 0))
            (define b (args-ref args 1))
	    (set! z (f (vector-ref regs a) (vector-ref regs b))))

          (define (z=ri f)
            (define a (args-ref args 0))
            (define b (check-imm (args-ref args 1)))
	    (set! z (f (vector-ref regs a) b)))

          (define (imm-shifter-carry imm)
            ;; The assembly-level IR does not record the immediate rotate.  For
            ;; constants that need no rotate, ARM preserves C; otherwise use the
            ;; canonical rotated immediate's bit 31.
            (if (and (number? imm) (>= imm 0) (< imm 256))
                old-carry
                (< (finitize-bit imm) 0)))

          (define (dp-calc kind op1 op2 sh-carry)
            (cond
             [(equal? kind 'add)
              (define result (finitize-bit (+ op1 op2)))
              (values result (add-flags op1 op2 #f result))]
             [(equal? kind 'adc)
              (define carry old-carry)
              (define result (finitize-bit (+ op1 op2 (bool->num carry))))
              (values result (add-flags op1 op2 carry result))]
             [(equal? kind 'sub)
              (define result (finitize-bit (- op1 op2)))
              (values result (sub-flags op1 op2 #f result))]
             [(equal? kind 'rsb)
              (define result (finitize-bit (- op2 op1)))
              (values result (sub-flags op2 op1 #f result))]
             [(equal? kind 'sbc)
              (define borrow (not old-carry))
              (define result (finitize-bit (- op1 op2 (bool->num borrow))))
              (values result (sub-flags op1 op2 borrow result))]
             [(equal? kind 'rsc)
              (define borrow (not old-carry))
              (define result (finitize-bit (- op2 op1 (bool->num borrow))))
              (values result (sub-flags op2 op1 borrow result))]
             [(equal? kind 'and)
              (define result (finitize-bit (bitwise-and op1 op2)))
              (values result (logical-flags result sh-carry z))]
             [(equal? kind 'orr)
              (define result (finitize-bit (bitwise-ior op1 op2)))
              (values result (logical-flags result sh-carry z))]
             [(equal? kind 'eor)
              (define result (finitize-bit (bitwise-xor op1 op2)))
              (values result (logical-flags result sh-carry z))]
             [(equal? kind 'bic)
              (define result (finitize-bit (bitwise-and op1 (bitwise-not op2))))
              (values result (logical-flags result sh-carry z))]
             [(equal? kind 'orn)
              (define result (finitize-bit (bitwise-ior op1 (bitwise-not op2))))
              (values result (logical-flags result sh-carry z))]
             [(equal? kind 'mov)
              (define result (finitize-bit op2))
              (values result (logical-flags result sh-carry z))]
             [(equal? kind 'mvn)
              (define result (finitize-bit (bitwise-not op2)))
              (values result (logical-flags result sh-carry z))]
             [else (assert #f (format "undefined data-processing op ~a" kind))]))

          (define (write-dp-result d kind op1 op2 sh-carry set-flags?)
            (define-values (result flags) (dp-calc kind op1 op2 sh-carry))
            (vector-set! regs d result)
            (when set-flags? (set! z flags)))

          (define (dp-rrr kind set-flags? [shf #t])
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define b (args-ref args 2))
            (define-values (op2 sh-carry)
              (if shf
                  (opt-shift b)
                  (values (vector-ref regs b) old-carry)))
            (write-dp-result d kind (vector-ref regs a) op2 sh-carry set-flags?))

          (define (dp-rri kind set-flags?)
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define imm (check-imm (args-ref args 2)))
            (write-dp-result d kind (vector-ref regs a) imm (imm-shifter-carry imm) set-flags?))

          (define (dp-mov kind set-flags? [shf #t])
            (define d (args-ref args 0))
            (define a (args-ref args 1))
            (define-values (op2 sh-carry)
              (if shf
                  (opt-shift a)
                  (values (vector-ref regs a) old-carry)))
            (write-dp-result d kind 0 op2 sh-carry set-flags?))

          (define (dp-movi kind set-flags?)
            (define d (args-ref args 0))
            (define imm (check-imm-mov (args-ref args 1)))
            (write-dp-result d kind 0 imm (imm-shifter-carry imm) set-flags?))

          (define (dp-test kind op1 op2 sh-carry)
            (define-values (result flags) (dp-calc kind op1 op2 sh-carry))
            (set! z flags))

          (define (dp-test-rr kind [shf #t])
            (define a (args-ref args 0))
            (define b (args-ref args 1))
            (define-values (op2 sh-carry)
              (if shf
                  (opt-shift b)
                  (values (vector-ref regs b) old-carry)))
            (dp-test kind (vector-ref regs a) op2 sh-carry))

          (define (dp-test-ri kind)
            (define a (args-ref args 0))
            (define imm (check-imm (args-ref args 1)))
            (dp-test kind (vector-ref regs a) imm (imm-shifter-carry imm)))

          (define (long-mul-acc signed? [set-flags? #f])
            (define d-lo (args-ref args 0))
            (define d-hi (args-ref args 1))
            (define a (args-ref args 2))
            (define b (args-ref args 3))
            (define hi (if signed? bvsmmul bvummul))
            (define product-lo (bvmul (vector-ref regs a) (vector-ref regs b)))
            (define val-lo (bvadd product-lo (vector-ref regs d-lo)))
            (define carry (add-carry-out product-lo
                                         (vector-ref regs d-lo)
                                         #f))
            (define val-hi (bvadd (bvadd (hi (vector-ref regs a) (vector-ref regs b))
                                         (vector-ref regs d-hi))
                                  (bool->num carry)))
            (vector-set! regs d-lo val-lo)
            (vector-set! regs d-hi val-hi)
            (when set-flags? (set! z (same-cv-flags64 val-lo val-hi z))))

          (cond
           ;; basic
           [(inst-eq `nop) (void)]
           [(inst-eq `add) (dp-rrr 'add #f)]
           [(inst-eq `adc) (dp-rrr 'adc #f)]
           [(inst-eq `sub) (dp-rrr 'sub #f)]
           [(inst-eq `rsb) (dp-rrr 'rsb #f)]
           [(inst-eq `sbc) (dp-rrr 'sbc #f)]
           [(inst-eq `rsc) (dp-rrr 'rsc #f)]

           [(inst-eq `and) (dp-rrr 'and #f)]
           [(inst-eq `orr) (dp-rrr 'orr #f)]
           [(inst-eq `eor) (dp-rrr 'eor #f)]
           [(inst-eq `bic) (dp-rrr 'bic #f)]
           [(inst-eq `orn) (dp-rrr 'orn #f)]

           [(inst-eq `adds) (dp-rrr 'add #t)]
           [(inst-eq `adcs) (dp-rrr 'adc #t)]
           [(inst-eq `subs) (dp-rrr 'sub #t)]
           [(inst-eq `rsbs) (dp-rrr 'rsb #t)]
           [(inst-eq `sbcs) (dp-rrr 'sbc #t)]
           [(inst-eq `rscs) (dp-rrr 'rsc #t)]

           [(inst-eq `ands) (dp-rrr 'and #t)]
           [(inst-eq `orrs) (dp-rrr 'orr #t)]
           [(inst-eq `eors) (dp-rrr 'eor #t)]
           [(inst-eq `bics) (dp-rrr 'bic #t)]

           ;; basic i
           [(inst-eq `add#) (dp-rri 'add #f)]
           [(inst-eq `adc#) (dp-rri 'adc #f)]
           [(inst-eq `sub#) (dp-rri 'sub #f)]
           [(inst-eq `rsb#) (dp-rri 'rsb #f)]
           [(inst-eq `sbc#) (dp-rri 'sbc #f)]
           [(inst-eq `rsc#) (dp-rri 'rsc #f)]

           [(inst-eq `and#) (dp-rri 'and #f)]
           [(inst-eq `orr#) (dp-rri 'orr #f)]
           [(inst-eq `eor#) (dp-rri 'eor #f)]
           [(inst-eq `bic#) (dp-rri 'bic #f)]
           [(inst-eq `orn#) (dp-rri 'orn #f)]

           [(inst-eq `adds#) (dp-rri 'add #t)]
           [(inst-eq `adcs#) (dp-rri 'adc #t)]
           [(inst-eq `subs#) (dp-rri 'sub #t)]
           [(inst-eq `rsbs#) (dp-rri 'rsb #t)]
           [(inst-eq `sbcs#) (dp-rri 'sbc #t)]
           [(inst-eq `rscs#) (dp-rri 'rsc #t)]

           [(inst-eq `ands#) (dp-rri 'and #t)]
           [(inst-eq `orrs#) (dp-rri 'orr #t)]
           [(inst-eq `eors#) (dp-rri 'eor #t)]
           [(inst-eq `bics#) (dp-rri 'bic #t)]
           
           ;; move
           [(inst-eq `mov) (dp-mov 'mov #f)]
           [(inst-eq `mvn) (dp-mov 'mvn #f)]
           [(inst-eq `movs) (dp-mov 'mov #t)]
           [(inst-eq `mvns) (dp-mov 'mvn #t)]
           
           ;; move i
           [(inst-eq `mov#) (dp-movi 'mov #f)]
           [(inst-eq `mvn#) (dp-movi 'mvn #f)]
           [(inst-eq `movs#) (dp-movi 'mov #t)]
           [(inst-eq `mvns#) (dp-movi 'mvn #t)]
           [(inst-eq `movt#) (r!i movhi)]
           [(inst-eq `movw#) (r!i movlo)]

           ;; reverse
           [(inst-eq `rev)   (rr bvrev)]
           [(inst-eq `rev16) (rr bvrev16)]
           [(inst-eq `revsh) (rr bvrevsh)]
           [(inst-eq `rbit)  (rr bvrbit)]

           ;; div & mul
           [(inst-eq `mul)  (rrr bvmul)]
           [(inst-eq `muls) (rrr-s bvmul)]
           [(inst-eq `mla)  (rrrr bvmla)]
           [(inst-eq `mlas) (rrrr-s bvmla)]
           [(inst-eq `mls)  (rrrr bvmls)]

           [(inst-eq `smmul) (rrr bvsmmul)]
           [(inst-eq `smmla) (rrrr bvsmmla)]
           [(inst-eq `smmls) (rrrr bvsmmls)]

           [(inst-eq `smull) (ddrr bvmul bvsmmul)]
           [(inst-eq `umull) (ddrr bvmul bvummul)]
           [(inst-eq `smulls) (ddrr bvmul bvsmmul #t)]
           [(inst-eq `umulls) (ddrr bvmul bvummul #t)]
           [(inst-eq `smlal) (long-mul-acc #t)]
           [(inst-eq `umlal) (long-mul-acc #f)]
           [(inst-eq `smlals) (long-mul-acc #t #t)]
           [(inst-eq `umlals) (long-mul-acc #f #t)]

           [(inst-eq `sdiv) (rrr bvsdiv)]
           [(inst-eq `udiv) (rrr bvudiv)]

           [(inst-eq `uxtah) (rrr uxtah)]
           [(inst-eq `uxth) (rr uxth)]
           [(inst-eq `uxtb) (rr uxtb)]
           
           ;; shift Rd, Rm, Rs
           ;; only the least significant byte of Rs is used.
           [(inst-eq `lsr) (rrr bvushr)]
           [(inst-eq `asr) (rrr bvshr)]
           [(inst-eq `lsl) (rrr bvshl)]
           [(inst-eq `ror) (rrr bvror)]
           
           ;; shift i
           [(inst-eq `lsr#) (rrb bvushr#)]
           [(inst-eq `asr#) (rrb bvshr#)]
           [(inst-eq `lsl#) (rrb bvshl#)]
           [(inst-eq `ror#) (rrb bvror#)]

           ;; bit
           [(inst-eq `bfc)  (r!bb  clrbit)]
           [(inst-eq `bfi)  (rrbb setbit)]

           ;; others
           [(inst-eq `sbfx) (rrbb sext)]
           [(inst-eq `ubfx) (rrbb ext)]
           [(inst-eq `clz)  (rr clz)]

           ;; load/store
           [(inst-eq `ldr#) (ldr #f)]
           [(inst-eq `str#) (str #f)]
           [(inst-eq `ldr)  (ldr #t)]
           [(inst-eq `str)  (str #t)]
           [(inst-eq `ldrb# `ldrh# `ldrsb# `ldrsh#) (ldr #f)]
           [(inst-eq `strb# `strh#) (str #f)]
           [(inst-eq `ldrb `ldrh `ldrsb `ldrsh) (ldr #t)]
           [(inst-eq `strb `strh) (str #t)]
           [(inst-eq `swp `swpb) (swp)]
           [(inst-eq `ldm#) (block-transfer #t)]
           [(inst-eq `stm#) (block-transfer #f)]

           ;; compare
           [(inst-eq `tst) (dp-test-rr 'and)]
           [(inst-eq `teq) (dp-test-rr 'eor)]
           [(inst-eq `cmp) (dp-test-rr 'sub)]
           [(inst-eq `cmn) (dp-test-rr 'add)]

           [(inst-eq `tst#) (dp-test-ri 'and)]
           [(inst-eq `teq#) (dp-test-ri 'eor)]
           [(inst-eq `cmp#) (dp-test-ri 'sub)]
           [(inst-eq `cmn#) (dp-test-ri 'add)]

           [else (assert #f "undefine instruction")]
           ))

	(define-syntax-rule (assert-op) (assert (and (>= op 0) (< op ninsts))))
        (assert (and (>= cond-type -1) (< cond-type (vector-length cond-opcodes))))
        (if (condition-holds? cond-type z) (exec) (assert-op))
        (assert (and (>= shfop -1) (< shfop (vector-length shf-opcodes))))
        )

      (for ([x program])
           (interpret-step x))
      
      (progstate regs (or memory (progstate-memory state)) z))

    (define (performance-cost code)
      (define cost 0)
      (define-syntax-rule (add-cost x) (set! cost (+ cost x)))
      (for ([x code])
           (let* ([ops-vec (inst-op x)]
                  [op (vector-ref ops-vec 0)]
                  [shfop (vector-ref ops-vec 2)]
                  [op-name (vector-ref base-opcodes op)]
                  [shfop-name (and (>= shfop 0) (vector-ref shf-opcodes shfop))]
                  )

             (define-syntax-rule (inst-eq a ...)
               (or (equal? a op-name) ...))
             (define-syntax-rule (shf-inst-eq a ...)
               (or (equal? a shfop-name) ...))

             (cond
              [(inst-eq `nop) (void)]
              [(inst-eq `str `str# `ldr `ldr# `strb `strb# `ldrb `ldrb#
                        `strh `strh# `ldrh `ldrh# `ldrsb `ldrsb# `ldrsh `ldrsh#)
               (add-cost 3)]
              [(inst-eq `swp `swpb) (add-cost 4)]
              [(inst-eq `ldm# `stm#) (add-cost 6)]
              [(inst-eq `mul `muls `mla `mlas `mls `smmul `smmla `smmls) (add-cost 5)]
              [(inst-eq `smull `umull `smulls `umulls
                        `smlal `umlal `smlals `umlals `sdiv `udiv)
               (add-cost 6)]
              [(inst-eq `tst `cmp `teq `cmn `tst# `cmp# `teq# `cmn#) (add-cost 2)]
              [(inst-eq `sbfx `ubfx `bfc `bfi) (add-cost 2)]
              ;; [(inst-eq `mov) 
              ;;  (cond
              ;;   [(shf-inst-eq `lsr `asr `lsl `ror) (add-cost 2)]
              ;;   [else (add-cost 1)])]

              ;; [(shf-inst-eq `lsr# `asr# `lsl# `ror#) (add-cost 2)]
              
              [(and (inst-eq `add `adc `sub `rsb `sbc `rsc `and `orr `eor `bic `orn `mov `mvn
                              `adds `adcs `subs `rsbs `sbcs `rscs `ands `orrs `eors `bics
                              `movs `mvns)
                    (shf-inst-eq `lsr `asr `lsl `ror))
               (add-cost 2)]

              [else (add-cost 1)])
             ))
      (when debug (pretty-display `(performance ,cost)))
      cost)

    (define legal-imm 
      (append (for/list ([i 12]) (arithmetic-shift #xff (* 2 i)))
              (list #xff000000 (- #xff000000))))

    (define-syntax-rule (check-imm x) 
      (assert-return 
       (ormap (lambda (i) (= (bitwise-and x i) (bitwise-and x mask))) legal-imm) 
       "illegal immediate"
       x))

    (define-syntax-rule (check-imm-mov x) 
      (assert-return 
       (or (= (bitwise-and x #xffff) x)
           (ormap (lambda (i) (= (bitwise-and x i) (bitwise-and x mask)))
                  legal-imm))
       "illegal mov immediate"
       x))

    ))
  
