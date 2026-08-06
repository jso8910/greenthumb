#lang racket

(require parser-tools/lex
         (prefix-in re- parser-tools/lex-sre)
         parser-tools/yacc
	 "../parser.rkt" "../inst.rkt")

(provide arm-parser%)

(define arm-parser%
  (class parser%
    (super-new)
    (inherit-field asm-parser asm-lexer)

    (define-tokens a (LABEL BLOCK WORD _WORD NUM REG NEGREG))
    (define-empty-tokens b (EOF TEXT COMMA DQUOTE HOLE HASH LSQBR RSQBR LBRACE RBRACE BANG NOP))

    (define-lex-trans number
      (syntax-rules ()
        ((_ digit)
         (re-: (uinteger digit)
               (re-? (re-: "." (re-? (uinteger digit))))))))

    (define-lex-trans uinteger
      (syntax-rules ()
        ((_ digit) (re-+ digit))))

    (define-lex-abbrevs
      (block-comment (re-: "; BB" number10 "_" number10 ":"))
      (line-comment (re-: (re-& (re-: ";" (re-* (char-complement #\newline)))
                                (complement (re-: block-comment any-string)))
                          #\newline))
      (digit10 (char-range "0" "9"))
      (number10 (number digit10))
      (snumber10 (re-or number10 (re-seq "-" number10)))
      (identifier-characters (re-or (char-range "A" "Z") (char-range "a" "z")))
      (identifier-characters-ext (re-or digit10 identifier-characters "_"))
      ;(identifier (re-+ identifier-characters))
      (identifier (re-seq identifier-characters 
                          (re-* (re-or identifier-characters digit10))))
      (identifier: (re-seq identifier ":"))
      (_identifier (re-seq "_" (re-* identifier-characters-ext)))
      (reg (re-or "fp" "ip" "lr" "sl" "sp" "pc" (re-seq "r" number10)))
      (negreg (re-seq "-" reg))
      )

    (set! asm-lexer
      (lexer-src-pos
       ("nop"      (token-NOP))
       (".text"    (token-TEXT))
       (","        (token-COMMA))
       ("\""       (token-DQUOTE))
       ("?"        (token-HOLE))
       ("#"        (token-HASH))
       ("["        (token-LSQBR))
       ("]"        (token-RSQBR))
       ("{"        (token-LBRACE))
       ("}"        (token-RBRACE))
       ("!"        (token-BANG))
       (negreg     (token-NEGREG lexeme))
       (reg        (token-REG lexeme))
       (identifier: (token-LABEL lexeme))
       (identifier (token-WORD lexeme))
       (_identifier (token-_WORD lexeme))
       (snumber10  (token-NUM lexeme))
       (block-comment (token-BLOCK lexeme))
       (line-comment (position-token-token (asm-lexer input-port)))
       (whitespace   (position-token-token (asm-lexer input-port)))
       ((eof) (token-EOF))))

    (set! asm-parser
      (parser
       (start code)
       (end EOF)
       (error
        (lambda (tok-ok? tok-name tok-value start-pos end-pos)
          (raise-syntax-error 'parser
                              (format "syntax error at '~a' in src l:~a c:~a"
                                      tok-name
                                      (position-line start-pos)
                                      (position-col start-pos)))))

       (tokens a b)
       (src-pos)
       (grammar

        (arg  ((REG) $1)
              ((REG BANG) (list 'base-wb $1))
              ((HASH NUM) $2)
              ((NUM) $1)
              ((WORD) $1))

	(arg-pair
	      ((WORD arg) (list $1 $2)))

        (offset ((arg) $1)
                ((NEGREG) $1))

        (memref ((LSQBR REG RSQBR) (list 'mem $2 #f #f #f))
                ((LSQBR REG RSQBR BANG) (list 'mem $2 #f #f #t))
                ((LSQBR REG COMMA offset RSQBR) (list 'mem $2 $4 #f #f))
                ((LSQBR REG COMMA offset RSQBR BANG) (list 'mem $2 $4 #f #t))
                ((LSQBR REG COMMA offset COMMA WORD HASH NUM RSQBR)
                 (list 'mem $2 $4 (list $6 $8) #f))
                ((LSQBR REG COMMA offset COMMA WORD HASH NUM RSQBR BANG)
                 (list 'mem $2 $4 (list $6 $8) #t))
                ((LSQBR REG COMMA offset COMMA WORD RSQBR)
                 (list 'mem $2 $4 (list $6 "0") #f))
                ((LSQBR REG COMMA offset COMMA WORD RSQBR BANG)
                 (list 'mem $2 $4 (list $6 "0") #t)))

        (reglist-inner ((REG) (list $1))
                       ((REG COMMA reglist-inner) (cons $1 $3)))

        (reglist ((LBRACE reglist-inner RBRACE) (list 'reglist $2)))

        (args ((arg) (list $1))
              ((NEGREG) (list $1))
	      ((arg-pair) $1)
              ((memref) (list $1))
              ((reglist) (list $1))
              ((arg COMMA args) (cons $1 $3))
              ((NEGREG COMMA args) (cons $1 $3))
	      ((arg-pair COMMA args) (append $1 $3))
              ((memref COMMA args) (cons $1 $3))
              ((reglist COMMA args) (cons $1 $3)))

        (instruction ((WORD args) (create-inst $1 (list->vector $2)))
		     ((WORD _WORD) (create-special-inst $1 $2))
                     ((NOP)       (create-inst "nop" (vector)))
		     ((HOLE) (inst #f #f)))

        (inst-list   (() (list))
                     ((instruction inst-list) (cons $1 $2)))

        (code   ((inst-list) (list->vector $1))
                )

        )))

    (define (create-special-inst op1 op2)
      (cond
       [(equal? op2 "__aeabi_idiv")
	(inst (vector "sdiv" "" "") (vector "r0" "r0" "r1"))]
       [(equal? op2 "__aeabi_uidiv")
	(inst (vector "udiv" "" "") (vector "r0" "r0" "r1"))]
       [else
	(raise (format "Undefine special instruction: ~a ~a" op1 op2))]))

    (define branch-condition-suffixes
      '("eq" "ne" "cs" "cc" "mi" "pl" "vs" "vc"
        "hi" "ls" "ge" "lt" "gt" "le" "al"))

    (define (branch-op? op)
      (or (member op '("b" "bl" "bx"))
          (for/or ([suffix branch-condition-suffixes])
                  (and (> (string-length op) (string-length suffix))
                       (equal? (substring op (- (string-length op)
                                                (string-length suffix)))
                               suffix)
                       (member (substring op 0 (- (string-length op)
                                                  (string-length suffix)))
                               '("b" "bl" "bx"))))))

    (define (first-token line)
      (define match (regexp-match #px"^\\s*([^;\\s]+)" line))
      (and match (cadr match)))

    (define (reject-branch-lines! source)
      (for ([line (string-split source "\n" #:trim? #f)]
            [line-number (in-naturals 1)])
           (define token (first-token line))
           (when (and token (branch-op? (string-downcase token)))
                 (raise-user-error
                  'arm-parser
                  "branches are unsupported: GreenThumb ARM optimization expects straight-line input, got ~a on line ~a"
                  token
                  line-number))))

    (define/override (ir-from-string s)
      (reject-branch-lines! s)
      (let ([input (open-input-string s)])
        (asm-parser
         (lambda ()
           (let ([token (asm-lexer input)])
             token)))))

    (define/override (ir-from-file file)
      (and (file-exists? file)
           (let ([source (file->string file)])
             (reject-branch-lines! source)
             (let ([input (open-input-string source)])
               (port-count-lines! input)
               (asm-parser
                (lambda ()
                  (let ([token (asm-lexer input)])
                    token)))))))

    (define (rename x)
      (cond
       [(equal? x "sb") "r9"]
       [(equal? x "sl") "r10"]
       [(equal? x "fp") "r11"]
       [(equal? x "ip") "r12"]
       [(equal? x "sp") "r13"]
       [(equal? x "lr") "r14"]
       [(equal? x "pc") "r15"]
       [else x]))

    (define (string-prefix? s prefix)
      (let ([s-len (string-length s)]
            [prefix-len (string-length prefix)])
        (and (>= s-len prefix-len)
             (equal? (substring s 0 prefix-len) prefix))))

    (define (string-suffix? s suffix)
      (let ([s-len (string-length s)]
            [suffix-len (string-length suffix)])
        (and (>= s-len suffix-len)
             (equal? (substring s (- s-len suffix-len)) suffix))))

    (define (reg-string? value)
      (and (string? value)
           (or (member value '("fp" "ip" "lr" "sl" "sp" "pc"))
               (and (> (string-length value) 1)
                    (equal? (substring value 0 1) "r")))))

    (define (negative-token? value)
      (and (string? value)
           (> (string-length value) 0)
           (equal? (substring value 0 1) "-")))

    (define (abs-token value)
      (if (negative-token? value)
          (substring value 1)
          value))

    (define (memref? value)
      (and (list? value) (pair? value) (equal? (car value) 'mem)))

    (define (reglist? value)
      (and (list? value) (pair? value) (equal? (car value) 'reglist)))

    (define (base-wb? value)
      (and (list? value) (pair? value) (equal? (car value) 'base-wb)))

    (define (reg-id reg)
      (define normalized (rename reg))
      (cond
        [(and (> (string-length normalized) 1)
              (equal? (substring normalized 0 1) "r"))
         (string->number (substring normalized 1))]
        [else #f]))

    (define (reglist-mask value)
      (cond
        [(reglist? value)
         (for/fold ([mask 0]) ([reg (cadr value)])
           (define id (reg-id reg))
           (if id (bitwise-ior mask (arithmetic-shift 1 id)) mask))]
        [(string? value) (string->number value)]
        [(number? value) value]
        [else #f]))

    (define (load-store-op? op)
      (member op '("ldr" "ldrb" "ldrh" "ldrsb" "ldrsh" "str" "strb" "strh")))

    (define (transfer-t-op op)
      (and (string-suffix? op "t")
           (let ([base (substring op 0 (sub1 (string-length op)))])
             (and (load-store-op? base) base))))

    (define (halfword-transfer-op? op)
      (member op '("ldrh" "ldrsb" "ldrsh" "strh")))

    (define (data-processing-immediate-op? op)
      (member op '("add" "adc" "sub" "rsb" "sbc" "rsc" "and" "orr" "eor" "bic" "orn"
                   "adds" "adcs" "subs" "rsbs" "sbcs" "rscs" "ands" "orrs" "eors" "bics"
                   "mov" "mvn" "movs" "mvns" "tst" "teq" "cmp" "cmn")))

    (define (shift-alias-op op)
      (cond
        [(member op '("asr" "lsl" "lsr" "ror")) (list "mov" op)]
        [(member op '("asrs" "lsls" "lsrs" "rors"))
         (list "movs" (substring op 0 (sub1 (string-length op))))]
        [(equal? op "rrx") (list "mov" "ror")]
        [(equal? op "rrxs") (list "movs" "ror")]
        [else #f]))

    (define (u32 value)
      (bitwise-and value #xffffffff))

    (define (ror32 value amount)
      (define shift (modulo amount 32))
      (if (= shift 0)
          (u32 value)
          (u32 (bitwise-ior (arithmetic-shift (u32 value) (- shift))
                            (arithmetic-shift (u32 value) (- 32 shift))))))

    (define (maybe-collapse-rotated-immediate op args)
      (define args-list (vector->list args))
      (if (and (data-processing-immediate-op? op)
               (>= (length args-list) 3)
               (let ([imm (string->number (list-ref args-list (- (length args-list) 2)))]
                     [rot (string->number (last args-list))])
                 (and imm rot
                      (not (reg-string? (list-ref args-list (- (length args-list) 2))))
                      (not (reg-string? (last args-list))))))
          (let* ([imm (string->number (list-ref args-list (- (length args-list) 2)))]
                 [rot (string->number (last args-list))]
                 [collapsed (format "~a, ~a" imm rot)])
            (list->vector (append (take args-list (- (length args-list) 2))
                                  (list collapsed))))
          args))

    (define (block-mode op)
      (cond
        [(or (equal? op "ldmda") (equal? op "stmda")) (list (substring op 0 3) "0" "0")]
        [(or (equal? op "ldmdb") (equal? op "stmdb")) (list (substring op 0 3) "1" "0")]
        [(or (equal? op "ldmia") (equal? op "stmia")) (list (substring op 0 3) "0" "1")]
        [(or (equal? op "ldmib") (equal? op "stmib")) (list (substring op 0 3) "1" "1")]
        [(or (equal? op "ldm") (equal? op "stm")) (list op "0" "1")]
        [else #f]))

    (define (memory-inst op cond-type args [force-post-writeback? #f])
      (define args-list (vector->list args))
      (define rd (first args-list))
      (define mem (second args-list))
      (define post-offset (and (>= (length args-list) 3) (third args-list)))
      (define rn (rename (second mem)))
      (define raw-offset (or post-offset (third mem) "0"))
      (define up? (not (negative-token? raw-offset)))
      (define offset (abs-token raw-offset))
	      (define shift (fourth mem))
	      (define shift-op (and shift (if (equal? (first shift) "rrx") "ror" (first shift))))
	      (define shift-arg (and shift (if (equal? (first shift) "rrx") "0" (second shift))))
	      (define post-shift-op (and post-offset (>= (length args-list) 4) (fourth args-list)))
	      (define post-shift-arg (and post-offset (>= (length args-list) 5) (fifth args-list)))
	      (define effective-shift-op
	        (cond
	          [shift shift-op]
	          [(equal? post-shift-op "rrx") "ror"]
	          [post-shift-op post-shift-op]
	          [else #f]))
	      (define effective-shift-arg
	        (cond
	          [shift shift-arg]
	          [(equal? post-shift-op "rrx") "0"]
	          [post-shift-arg post-shift-arg]
	          [else "0"]))
	      (define pre? (not post-offset))
	      (define wb? (or (and pre? (fifth mem))
	                      (and force-post-writeback? (not pre?))))
      (define reg-offset? (reg-string? (abs-token offset)))
      (define full-op (string-append op "-full"))
	      (define normalized-offset (rename (abs-token offset)))
	      (cond
		        [(and reg-offset? (not (halfword-transfer-op? op)))
		         (inst (vector full-op cond-type (if effective-shift-op effective-shift-op "lsl"))
	               (list->vector
	                (map rename
	                     (list rd rn normalized-offset
	                           (if pre? "1" "0")
	                           (if up? "1" "0")
	                           (if wb? "1" "0")
	                           effective-shift-arg))))]
        [(and reg-offset? (halfword-transfer-op? op))
         (inst (vector full-op cond-type "||")
               (list->vector
                (map rename
                     (list rd rn normalized-offset
                           (if pre? "1" "0")
                           (if up? "1" "0")
                           (if wb? "1" "0")))))]
        [else
         (inst (vector full-op cond-type "")
               (list->vector
                (map rename
                     (list rd rn normalized-offset
                           (if pre? "1" "0")
                           (if up? "1" "0")
                           (if wb? "1" "0")))))]))

	    (define (block-inst mode cond-type args)
	      (define args-list (vector->list args))
	      (define base-arg (first args-list))
	      (define rn (if (base-wb? base-arg) (cadr base-arg) base-arg))
	      (define w (if (base-wb? base-arg) "1" "0"))
      (define mask (reglist-mask (second args-list)))
      (inst (vector (string-append (first mode) "-full") cond-type "")
            (vector (rename rn)
                    (number->string mask)
	                    (second mode)
	                    (third mode)
	                    w)))

	    (define (stack-block-inst op cond-type args)
	      (define regmask (reglist-mask (vector-ref args 0)))
	      (cond
	        [(equal? op "push")
	         (inst (vector "stm-full" cond-type "")
	               (vector "r13" (number->string regmask) "1" "0" "1"))]
	        [(equal? op "pop")
	         (inst (vector "ldm-full" cond-type "")
	               (vector "r13" (number->string regmask) "0" "1" "1"))]
	        [else #f]))

	    (define (post-index-memory-rrx? args args-len)
	      (and (>= args-len 4)
	           (equal? (vector-ref args (sub1 args-len)) "rrx")
	           (>= args-len 2)
	           (memref? (vector-ref args 1))))

    (define (create-inst op args)
      (define args-len (vector-length args))
      (cond
	       [(and (>= args-len 4)
	             (not (and (>= args-len 2)
	                       (memref? (vector-ref args 1))))
		     (member (string->symbol (vector-ref args (- args-len 2)))
	                     '(asr asl lsr lsl ror)))

        (define shfop (vector-ref args (- args-len 2)))
        (when (equal? shfop "asl") (set! shfop "lsl"))

        (define base (create-inst op (vector-append (vector-copy args 0 (- args-len 2))
                                                    (vector (vector-ref args (- args-len 1))))))
        (define ops-vec (inst-op base))
        (vector-set! ops-vec 2 shfop)
        base]

       [else
	(when (equal? op "asl") (set! op "lsl"))
        (when (branch-op? op)
              (raise-user-error
               'arm-parser
               "branches are unsupported: GreenThumb ARM optimization expects straight-line input, got ~a"
               op))
	(define op-len (string-length op))
	;; Determine type
	(define cond-type (if (>= op-len 2) (substring op (- op-len 2)) ""))
        (define cond-looking-op?
          (member op (list "smmls" "adcs" "sbcs" "rscs" "bics" "movs"
                           "asrs" "lsls" "lsrs" "rors" "rrxs"
                           "muls" "mlas" "smulls" "umulls" "smlal"
                           "umlal" "smlals" "umlals")))
	(define cond?
          (and (member cond-type (list "eq" "ne" "cs" "cc" "mi" "pl" "vs" "vc"
                                        "hi" "ls" "ge" "lt" "gt" "le" "al"))
               (> op-len 3)
               (not cond-looking-op?)))
	;; ls
	(set! cond-type (if cond? cond-type ""))
	(when cond? (set! op (substring op 0 (- op-len 2))))

        (set! args (maybe-collapse-rotated-immediate op args))
        (set! args-len (vector-length args))

        (define mode (block-mode op))
        (define shift-alias (shift-alias-op op))
        (define t-op (transfer-t-op op))
	        (cond
	          [(and (member op '("push" "pop"))
	                (= args-len 1)
	                (reglist? (vector-ref args 0)))
	           (stack-block-inst op cond-type args)]
	          [mode
	           (block-inst mode cond-type args)]
          [(and (member op '("swp" "swpb"))
                (= args-len 3)
                (memref? (vector-ref args 2)))
           (define mem (vector-ref args 2))
           (inst (vector op cond-type "")
                 (vector (rename (vector-ref args 0))
                         (rename (vector-ref args 1))
                         (rename (second mem))))]
          [(and shift-alias (= args-len 3))
           (define shfop (second shift-alias))
           (define normalized-op (first shift-alias))
           (inst (vector normalized-op cond-type shfop) (vector-map rename args))]
          [(and shift-alias (= args-len 2))
           (define shfop (second shift-alias))
           (define normalized-op (first shift-alias))
           (inst (vector normalized-op cond-type "ror")
                 (vector (rename (vector-ref args 0))
                         (rename (vector-ref args 1))
                         "0"))]
	          [(and (>= args-len 3)
	                (equal? (vector-ref args (sub1 args-len)) "rrx")
	                (not (post-index-memory-rrx? args args-len)))
	           (inst (vector op cond-type "ror")
	                 (vector-append (vector-map rename (vector-copy args 0 (sub1 args-len)))
	                                (vector "0")))]
          [(and t-op
                (>= args-len 2)
                (memref? (vector-ref args 1)))
           (memory-inst t-op cond-type args #t)]
          [(and (load-store-op? op)
                (>= args-len 2)
                (memref? (vector-ref args 1)))
           (memory-inst op cond-type args)]
          [else
	   ;; for ldr & str, fp => r99, divide offset by 4
	   (when (or (equal? op "str") (equal? op "ldr"))
	         (define offset (vector-ref args 2))
	         (unless (equal? (substring offset 0 1) "r")
		         (vector-set! 
		          args 2
		          (number->string (quotient (string->number offset) 4)))))

           (inst (vector op cond-type "") (vector-map rename args))])]))

    (define/public (liveness-from-file file)
      (define in-port (open-input-file file))
      (define liveness-map (make-hash))
      (define (parse)
        (define line (read-line in-port))
        (unless (equal? eof line)
                (define match (regexp-match-positions #rx":" line))
                (when match
                      (define pos (cdar match))
                      (define live-regs (map (lambda (x) (string->number (string-trim x)))
                                             (string-split (substring line pos) ",")))
                      (hash-set! liveness-map (substring line 0 pos) live-regs))
                (parse)))
      (parse)
      liveness-map)

    (define/override (info-from-file file)
      (define (parse-live-out-token token)
        (define number (string->number token))
        (cond
         [number number]
         [(member token '("memory" "z" "flag" "flags" "nzcv" "n" "c" "v"))
          (string->symbol token)]
         [else token]))
      (define lines (file->lines file))
      (define live-out (map (lambda (x) (parse-live-out-token (string-trim x)))
                            (string-split (first lines) ",")))
      live-out)

    ))
