#lang racket

(require "../printer.rkt" 
         "../inst.rkt"
         "arm-machine.rkt")

(provide arm-printer%)

(define arm-printer%
  (class printer%
    (super-new)
    (inherit-field machine report-mutations)
    (override encode-inst decode-inst print-struct-inst print-syntax-inst
              compress-state-space decompress-state-space
              output-constraint-string)

    (define (print-struct-inst x [indent ""])
      (pretty-display (format "~a(inst ~a ~a)" indent (inst-op x) (inst-args x))))

    (define (print-syntax-inst x [indent ""])
      (define ops-vec (inst-op x))
      (define args (vector-copy (inst-args x)))

      (define op (vector-ref ops-vec 0))
      
      (define shfop (vector-ref ops-vec 2))
      
      (when (or (equal? op "str") (equal? op "ldr"))
	    (when (equal? "r11" (vector-ref args 1))
                  (vector-set! args 1 "fp"))
	    (when (not (equal? (substring (vector-ref args 2) 0 1) "r"))
		  (vector-set! args 2 (number->string (* 4 (string->number (vector-ref args 2)))))))

      (define args-list (vector->list args))
      (define len (length args-list))
      (define (string-suffix? s suffix)
        (let ([s-len (string-length s)]
              [suffix-len (string-length suffix)])
          (and (>= s-len suffix-len)
               (equal? (substring s (- s-len suffix-len)) suffix))))
      (define (string-prefix? s prefix)
        (let ([s-len (string-length s)]
              [prefix-len (string-length prefix)])
          (and (>= s-len prefix-len)
               (equal? (substring s 0 prefix-len) prefix))))
      (define (reg? s)
        (and (string? s)
             (or (equal? s "fp")
                 (and (> (string-length s) 1)
                      (equal? (substring s 0 1) "r")))))
      (define (bool-one? s)
        (or (equal? s "1") (equal? s 1)))
      (define (imm-arg s)
        (if (and (string? s) (not (string-prefix? s "#")))
            (string-append "#" s)
            s))
      (define (strip-full-op s)
        (let* ([without-imm (if (string-suffix? s "#")
                                (substring s 0 (sub1 (string-length s)))
                                s)]
               [without-full (regexp-replace #rx"-full$" without-imm "")])
          without-full))
      (define (signed-offset offset up?)
        (if up?
            (imm-arg offset)
            (imm-arg (string-append "-" offset))))
      (define (reg-offset offset up? shfop shfarg)
        (define base (if up? offset (string-append "-" offset)))
        (cond
          [(and (equal? shfop "ror") (equal? shfarg "0"))
           (format "~a, rrx" base)]
          [(and shfop
                (not (equal? shfop ""))
                (not (equal? shfop "||"))
                shfarg
                (not (and (equal? shfop "lsl") (equal? shfarg "0"))))
           (format "~a, ~a #~a" base shfop shfarg)]
          [else base]))
      (define (transfer-addr rn offset p u w register-offset?)
        (define offset-text
          (if register-offset?
              (reg-offset offset u shfop (and (> len 6) (list-ref args-list 6)))
              (signed-offset offset u)))
        (cond
          [p
           (format "[~a, ~a]~a" rn offset-text (if w "!" ""))]
          [else
           (format "[~a], ~a" rn offset-text)]))
      (define (reglist-text mask)
        (define parsed-mask (if (number? mask) mask (string->number mask)))
        (format "{~a}"
                (string-join
                 (for/list ([i (in-range 16)]
                            #:when (= (bitwise-bit-field parsed-mask i (add1 i)) 1))
                   (format "r~a" i))
                 ", ")))
      (define (block-suffix p u)
        (cond
          [(and p u) "ib"]
          [(and p (not u)) "db"]
          [(and (not p) u) "ia"]
          [else "da"]))
      (define (full-transfer-op? s)
        (regexp-match? #rx"^(ldr|ldrb|ldrh|ldrsb|ldrsh|str|strb|strh)-full#?$" s))
      (define (block-transfer-op? s)
        (regexp-match? #rx"^(ldm|stm)-full#?$" s))
      (define (simple-transfer-op? s)
        (member s '("ldr" "ldrb" "ldrh" "ldrsb" "ldrsh" "str" "strb" "strh")))
      (define (simple-transfer-addr rn offset)
        (format "[~a, ~a]" rn (if (reg? offset) offset (imm-arg offset))))
      (define (dp-immediate-op? s)
        (member s '("add" "adc" "sub" "rsb" "sbc" "rsc" "and" "orr" "eor" "bic" "orn"
                    "adds" "adcs" "subs" "rsbs" "sbcs" "rscs" "ands" "orrs" "eors" "bics"
                    "mov" "mvn" "movs" "mvns" "tst" "teq" "cmp" "cmn")))
      (cond
       [(equal? op "nop") (display "nop")]
       [(member op '("swp" "swpb"))
        (display (format "~a~a~a ~a, ~a, [~a]"
                         indent op (vector-ref ops-vec 1)
                         (list-ref args-list 0)
                         (list-ref args-list 1)
                         (list-ref args-list 2)))]
       [(full-transfer-op? op)
        (define register-offset? (and (>= len 6) (reg? (list-ref args-list 2))))
        (define p (bool-one? (list-ref args-list 3)))
        (define w (bool-one? (list-ref args-list 5)))
        (define mnemonic (format "~a~a~a"
                                 (strip-full-op op)
                                 (if (and (not p) w) "t" "")
                                 (vector-ref ops-vec 1)))
        (define addr (transfer-addr (list-ref args-list 1)
                                    (list-ref args-list 2)
                                    p
                                    (bool-one? (list-ref args-list 4))
                                    w
                                    register-offset?))
        (display (format "~a~a ~a, ~a" indent mnemonic (list-ref args-list 0) addr))]
       [(block-transfer-op? op)
        (define p (bool-one? (list-ref args-list 2)))
        (define u (bool-one? (list-ref args-list 3)))
        (define w (bool-one? (list-ref args-list 4)))
        (define mnemonic (format "~a~a~a"
                                 (substring op 0 3)
                                 (block-suffix p u)
                                 (vector-ref ops-vec 1)))
        (display (format "~a~a ~a~a, ~a"
                         indent
                         mnemonic
                         (list-ref args-list 0)
                         (if w "!" "")
                         (reglist-text (list-ref args-list 1))))]
       [(and (simple-transfer-op? op) (= len 3))
        (display (format "~a~a~a ~a, ~a"
                         indent
                         op
                         (vector-ref ops-vec 1)
                         (list-ref args-list 0)
                         (simple-transfer-addr (list-ref args-list 1)
                                               (list-ref args-list 2))))]
       [(and shfop (not (equal? shfop "")))
        (display (format "~a~a~a ~a" indent op (vector-ref ops-vec 1)
                         (string-join (take args-list (sub1 len)) ", ")))
        (if (and (equal? shfop "ror") (equal? (last args-list) "0"))
            (display ", rrx")
            (display (format ", ~a ~a" shfop
                             (if (reg? (last args-list))
                                 (last args-list)
                                 (imm-arg (last args-list))))))]
       [(and (dp-immediate-op? op) (> len 0) (not (reg? (last args-list))))
        (display (format "~a~a~a ~a" indent op (vector-ref ops-vec 1)
                         (string-join (append (take args-list (sub1 len))
                                              (list (imm-arg (last args-list))))
                                      ", ")))]
       [else 
        (display (format "~a~a~a ~a" indent op (vector-ref ops-vec 1)
                         (string-join args-list ", ")))])
      (newline))

    (define (name->id name)
      ;;(pretty-display `(name->id ,name))
      (cond
       [(string->number name)
        (string->number name)]
       
       [(and (> (string-length name) 1) (equal? (substring name 0 1) "r"))
        (string->number (substring name 1))]

       [(equal? name "fp") "fp"]

       [(regexp-match? #rx"," name) name]
       
       [else 
        (raise (format "encode: name->id: undefined for ~a" name))]))

    ;; Convert an instruction in string format into
    ;; an instruction encoded using numbers.
    (define (encode-inst x)
      (define ops-vec (inst-op x))
      (cond
       [(not ops-vec) x]
       [else
        (define args (inst-args x))
        (define op0 (vector-ref ops-vec 0))
        (define shfop (vector-ref ops-vec 2))
	(define args-len (vector-length args))
	(when (and (> args-len 0)
		   (not (equal? "r" (substring (vector-ref args (sub1 args-len)) 0 1)))
                   (or (not shfop) (equal? shfop ""))
		   (not (member (string->symbol op0) '(bfc bfi sbfx ubfx))))
	      (set! op0 (string-append op0 "#")))
        
	(define shfarg (and (> args-len 0) (vector-ref args (sub1 args-len))))
	(when (and shfarg (not (equal? "r" (substring shfarg 0 1))))
	      (set! shfop (string-append shfop "#")))

        (define cond-type (vector-ref ops-vec 1))
        (inst (vector (send machine get-base-opcode-id (string->symbol op0))
                      (send machine get-cond-opcode-id (string->symbol cond-type))
                      (send machine get-shf-opcode-id (string->symbol shfop)))
              (vector-map name->id args))]))
                
    ;; Convert an instruction encoded using numbers
    ;; into an instruction in string format.
    (define (decode-inst x)
      (define ops-vec (inst-op x))
      (define args (inst-args x))

      (define test (send machine has-opcode-id? ops-vec))
      (unless test
              (vector-set! ops-vec 2 -1)
              (set! test (send machine has-opcode-id? ops-vec)))
      (unless test
              (vector-set! ops-vec 1 -1)
              (set! test (send machine has-opcode-id? ops-vec)))
      
      (define (convert-op op)
	(let* ([str (symbol->string op)]
	       [len (string-length str)])
	  (if (and (> len 0) (equal? (substring str (sub1 len)) "#"))
	      (substring str 0 (sub1 len))
	      str)))
      
      (define opcode (convert-op (send machine get-base-opcode-name (vector-ref ops-vec 0))))
      ;;(pretty-display `(op ,opcode))
      (define condtype (convert-op (send machine get-cond-opcode-name (vector-ref ops-vec 1))))
      (define shfop (convert-op (send machine get-shf-opcode-name (vector-ref ops-vec 2))))


      (define new-args
        (for/vector ([arg args] [type (send machine get-arg-types ops-vec)])
                     (cond
                      [(member type '(reg reg-sp)) (format "r~a" arg)]
                      [(number? arg) (number->string arg)]
                      [else arg])))

      (inst (vector opcode condtype shfop) new-args))

    ;;;;;;;;;;;;;;;;;;;;;;; For compressing reg space ;;;;;;;;;;;;;;;;;;;;
    (define (inner-rename x reg-map)
      (define (register-rename r)
        (cond
         [(and r (> (string-length r) 1) (equal? (substring r 0 1) "r"))
          (format "r~a" (vector-ref reg-map (string->number (substring r 1))))]
         
         [else r]))

      (define new-args
        (for/vector ([arg (inst-args x)]) (register-rename arg)))

      (inst (inst-op x) new-args))

    ;; Input
    ;; program: string IR format
    ;; Output
    ;; 1) compressed program in the same format as input
    ;; 2) compressed live-out
    ;; 3) map-back
    ;; 4) program state config
    (define (compress-state-space program live-out)
      (define reg-set (mutable-set))
      (define max-reg 0)

      ;; Collect all used register ids.
      (define (collect-reg-id! reg-id)
        (when (number? reg-id)
              (set-add! reg-set reg-id)
              (when (> reg-id max-reg) (set! max-reg reg-id))))

      (define (collect-reglist! mask)
        (define parsed-mask
          (cond
           [(number? mask) mask]
           [(string? mask) (string->number mask)]
           [else #f]))
        (when (number? parsed-mask)
              (for ([reg-id (in-range 16)])
                   (when (= (bitwise-bit-field parsed-mask reg-id (add1 reg-id)) 1)
                         (collect-reg-id! reg-id)))))

      (define (inner-collect x)
	(define (f r)
	  (when (and r (> (string-length r) 1) (equal? (substring r 0 1) "r"))
		(collect-reg-id! (string->number (substring r 1)))))

        (for ([args (inst-args x)])
             (and args (for ([arg args]) (f args)))))

      (define (inner-collect-reglist x)
        (define op (vector-ref (inst-op x) 0))
        (define args (inst-args x))
        (when (and (member op '("ldm" "stm" "ldm-full" "stm-full"))
                   (>= (vector-length args) 2))
              (collect-reglist! (vector-ref args 1))))

      (for ([x program]) (inner-collect x))
      (for ([x program]) (inner-collect-reglist x))
      (for ([live live-out])
           (when (number? live) (collect-reg-id! live)))

      ;; The ARM simulators model r15 specially as the symbolic PC base.
      ;; Keep it at compressed register id 15 so PC reads survive compression.
      (when (set-member? reg-set 15)
            (for ([reg-id (in-range 15)])
                 (collect-reg-id! reg-id)))

      (define stack-config (send machine get-stack-scratch-config))
      (when stack-config
            (define sp-reg (list-ref stack-config 0))
            (set-add! reg-set sp-reg)
            (when (> sp-reg max-reg) (set! max-reg sp-reg)))

      ;; Reserve real ARM registers for scratch use before compression.  These
      ;; registers are not live-in/out, but must exist in the compressed
      ;; machine config so stochastic search can choose them as temporaries.
      (define requested-min-scratch-regs (send machine get-min-scratch-regs))
      (define (collect-scratch-regs reg-id scratch-regs)
        (cond
         [(= (length scratch-regs) requested-min-scratch-regs) (reverse scratch-regs)]
         [(>= reg-id 15) (reverse scratch-regs)]
         [(set-member? reg-set reg-id)
          (collect-scratch-regs (add1 reg-id) scratch-regs)]
         [else
          (collect-scratch-regs (add1 reg-id) (cons reg-id scratch-regs))]))
      (define scratch-regs (collect-scratch-regs 0 '()))
      (when (< (length scratch-regs) requested-min-scratch-regs)
            (eprintf
             "WARNING: compress-state-space: requested ~a scratch register(s), but only ~a non-PC ARM register(s) are free; continuing with ~a.\n"
             requested-min-scratch-regs
             (length scratch-regs)
             (length scratch-regs))
            (flush-output (current-error-port))
            (send machine set-min-scratch-regs! (length scratch-regs)))
      (for ([reg-id scratch-regs])
           (collect-reg-id! reg-id))

      ;; Keep architectural stack registers at their real ids.  Block-transfer
      ;; register lists are raw bitmasks, so dense renumbering is especially
      ;; error-prone for push/pop-style code that mentions sp/lr.
      (cond
       [(set-member? reg-set 14)
        (for ([reg-id (in-range 15)]) (collect-reg-id! reg-id))]
       [(set-member? reg-set 13)
        (for ([reg-id (in-range 14)]) (collect-reg-id! reg-id))])

      ;; Construct register map from original to compressed version.
      (define reg-map (make-vector (add1 max-reg) #f))
      (define id 0)
      (for ([i 32])
           (when (set-member? reg-set i)
                 (vector-set! reg-map i id)
                 (set! id (add1 id))))

      ;; Construct register map from compressed back to original version. +2 regs
      (define reg-map-back (make-vector id))
      (set! id 0)
      (for ([i 32])
           (when (set-member? reg-set i)
                 (vector-set! reg-map-back id i)
                 (set! id (add1 id))))

      ;; Generate outputs.
      (define compressed-program
        (vector-map (lambda (x) (inner-rename x reg-map)) program))

      (define live-out-extra (filter symbol? live-out))
      (define compressed-live-out 
        (map (lambda (x) (vector-ref reg-map x)) 
             (filter (lambda (x) (and (number? x) (<= x max-reg) (vector-ref reg-map x))) 
                     live-out)))

      (values compressed-program
              (append compressed-live-out live-out-extra)
              reg-map-back id))

    (define (decompress-state-space program reg-map)
      (vector-map (lambda (x) (inner-rename x reg-map)) program))

    (define/public (encode-live x)
      (define reg (make-vector (send machine get-config) #f))
      (define memory #f)
      (define n #f)
      (define z #f)
      (define c #f)
      (define v #f)
      (for ([i x])
           (cond
            [(number? i) (vector-set! reg i #t)]
            [(equal? i 'memory) (set! memory #t)]
            [(equal? i 'n) (set! n #t)]
            [(equal? i 'z) (set! z #t)]
            [(equal? i 'c) (set! c #t)]
            [(equal? i 'v) (set! v #t)]
            [(member i '(flag flags nzcv))
             (set! n #t)
             (set! z #t)
             (set! c #t)
             (set! v #t)]))
      (progstate reg memory n z c v))

    
    ;; Convert live-out (which is one of the outputs from 
    ;; parser::info-from-file) into string. 
    (define (output-constraint-string live-out)
      (format "(send printer encode-live '~a)" live-out))

    ))
