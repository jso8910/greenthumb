#lang racket

(require "../stochastic.rkt"
         "../inst.rkt"
         "../machine.rkt" "../memory-racket.rkt" "arm-machine.rkt")

(provide arm-stochastic%)

(define arm-stochastic%
	  (class stochastic%
	    (super-new)
	    (inherit-field machine stat mutate-dist live-in)
	    (inherit mutate pop-count32 correctness-cost-base
	             inst-copy-with-op inst-copy-with-args)
	    (override superoptimize correctness-cost
	              random-instruction random-args-from-op mutate-operand
	              )
    (set! mutate-dist
          #hash((opcode . 2) (operand . 1) (swap . 1) (instruction . 1)))
	  

	    (define bit (get-field bitwidth machine))
	    (define flag-output-live? #f)
	    (define flag-opcode-bias 0.75)
	    (define flag-writing-opcodes
	      '(adds adcs subs rsbs sbcs rscs
	        adds# adcs# subs# rsbs# sbcs# rscs#
	        ands orrs eors bics
	        ands# orrs# eors# bics#
	        movs mvns movs# mvns#
	        tst cmp teq cmn tst# cmp# teq# cmn#))

	    (define (base-opcode-name opcode-id)
	      (define opcode-name (send machine get-opcode-name opcode-id))
	      (if (vector? opcode-name)
	          (vector-ref opcode-name 0)
	          opcode-name))

	    (define (flag-writing-opcode? opcode-id)
	      (member (base-opcode-name opcode-id) flag-writing-opcodes))

	    (define (prefer-flag-opcodes opcode-pool)
	      (define flag-pool (filter flag-writing-opcode? opcode-pool))
	      ;; When NZCV is live-out, most non-flag-writing instructions sit on
	      ;; a very flat stochastic plateau: they preserve old flags and are
	      ;; usually equally wrong.  Biasing random generation and opcode
	      ;; mutation toward flag-writing/test opcodes gives the search a way
	      ;; to discover candidates such as `subs ...` for `cmp ...`, while
	      ;; still leaving the full restriction-filtered opcode pool reachable.
	      (if (and flag-output-live?
	               (not (empty? flag-pool))
	               (< (random) flag-opcode-bias))
	          flag-pool
	          opcode-pool))

	    (define (any-flag-live? state)
	      (or (progstate-n state)
	          (progstate-zf state)
	          (progstate-c state)
	          (progstate-v state)))

	    (define (flag-bit-cost expected actual live?)
	      (if live?
	          (if (equal? expected actual) 0 1)
	          0))

	    (define (nonempty-list? xs)
	      (and (list? xs) (not (empty? xs))))

	    (define (memory-immediate-op? op-name)
	      (member op-name '(ldr# str# ldrh# strh#)))

	    (define (register-offset-op-name op-name)
	      (case op-name
	        [(ldr#) 'ldr]
	        [(str#) 'str]
	        [(ldrh#) 'ldrh]
	        [(strh#) 'strh]
	        [else #f]))

	    (define (memory-byte-offset op-name raw-offset)
	      (and (number? raw-offset)
	           (case op-name
	             [(ldr# str#) (* 4 raw-offset)]
	             [(ldrh# strh#) raw-offset]
	             [else #f])))

	    (define (fresh-temp-reg used-regs)
	      (for/or ([reg (in-range (send machine get-config))])
	              (and (not (member reg used-regs)) reg)))

	    (define (materialized-memory-offset-seed spec)
	      (and (= (vector-length spec) 1)
	           (let* ([source (vector-ref spec 0)]
	                  [source-op (inst-op source)]
	                  [source-args (inst-args source)]
	                  [op-name (send machine get-base-opcode-name
	                                 (vector-ref source-op 0))]
	                  [replacement-op-name (register-offset-op-name op-name)])
	             (and replacement-op-name
	                  (memory-immediate-op? op-name)
	                  (= (vector-length source-args) 3)
	                  (let* ([byte-offset
	                          (memory-byte-offset op-name (vector-ref source-args 2))]
	                         [tmp
	                          (fresh-temp-reg
	                           (remove-duplicates
	                            (filter number?
	                                    (vector->list
	                                     (vector-copy source-args 0 2)))))]
	                         [cond-id (vector-ref source-op 1)]
	                         [mov-op
	                          (vector (send machine get-base-opcode-id 'mov#)
	                                  cond-id
	                                  -1)]
	                         [replacement-op
	                          (vector (send machine get-base-opcode-id replacement-op-name)
	                                  cond-id
	                                  -1)])
	                    (and byte-offset
	                         (not (= byte-offset 0))
	                         tmp
	                         (let ([candidate
	                                (vector
	                                 (inst mov-op (vector tmp byte-offset))
	                                 (inst replacement-op
	                                       (vector (vector-ref source-args 0)
	                                               (vector-ref source-args 1)
	                                               tmp)))])
	                           (and (send machine program-allowed? candidate)
	                                candidate))))))))

	    (define (size-allows-materialized-offset-seed? size)
	      (define numeric-size
	        (cond
	          [(number? size) size]
	          [(string? size) (string->number size)]
	          [else #f]))
	      (or (not numeric-size) (>= numeric-size 2)))

	    (define (superoptimize spec constraint
	                           name time-limit size
	                           #:prefix [prefix (vector)]
	                           #:postfix [postfix (vector)]
	                           #:assume [assumption (send machine no-assumption)]
	                           #:input-file [input-file #f]
	                           #:start-prog [start #f])
	      (set! flag-output-live? (and (any-flag-live? constraint) #t))
	      (define seeded-start
	        (or start
	            (and (size-allows-materialized-offset-seed? size)
	                 (materialized-memory-offset-seed spec))))
	      (super superoptimize spec constraint
	             name time-limit size
	             #:prefix prefix
	             #:postfix postfix
	             #:assume assumption
	             #:input-file input-file
	             #:start-prog seeded-start))

	    (define (u32-random)
	      (bitwise-ior (arithmetic-shift (random 65536) 16)
	                   (random 65536)))

	    (define (finitize-local value)
	      (define mask (sub1 (arithmetic-shift 1 bit)))
	      (define masked (bitwise-and value mask))
	      (if (bitwise-bit-set? masked (sub1 bit))
	          (bitwise-ior masked (arithmetic-shift -1 bit))
	          masked))

	    (define (dedupe xs)
	      (reverse (remove-duplicates xs)))

	    (define (const-candidates seed-values)
	      (define seeds (filter number? seed-values))
	      (dedupe
	       (append
	        seeds
	        (range 256)
	        '(-1 -2 -4 -8 -16)
	        (for/list ([v seeds]) (quotient v 2))
	        (for/list ([v seeds]) (- v))
	        (for/list ([v seeds]) (add1 v))
	        (for/list ([v seeds]) (sub1 v))
	        (for/list ([v seeds]) (arithmetic-shift v -1)))))

	    (define (source-derived-consts seed-values)
	      (define seeds (filter number? seed-values))
	      (dedupe
	       (append
	        seeds
	        (for/list ([v seeds]) (quotient v 2))
	        (for/list ([v seeds]) (- v))
	        (for/list ([v seeds]) (add1 v))
	        (for/list ([v seeds]) (sub1 v))
	        (for/list ([v seeds]) (arithmetic-shift v -1))
	        (for/list ([v seeds]) (arithmetic-shift v 1)))))

	    (define (random-const seed-values [old #f])
	      (define derived (source-derived-consts seed-values))
	      (define pool (const-candidates seed-values))
	      (define sample
	        (cond
	          [(and (not (empty? derived)) (< (random) 0.55))
	           (random-from-list derived)]
	          [(< (random) 0.90) (random-from-list pool)]
	          [else (finitize-local (u32-random))]))
	      (if (and old (= sample old) (> (length pool) 1))
	          (random-const seed-values old)
	          sample))

	    (define (random-bit-amount seed-values [old #f])
	      (define pool
	        (dedupe
	         (append (filter number? seed-values)
	                 (range (add1 bit)))))
	      (define sample (random-from-list pool))
	      (if (and old (= sample old) (> (length pool) 1))
	          (random-bit-amount seed-values old)
	          sample))

	    (define (random-value-for-type type range [old #f])
	      (define seeds (if (vector? range) (vector->list range) '()))
	      (cond
	        [(equal? type 'const) (random-const seeds old)]
	        [(equal? type 'bit) (random-bit-amount seeds old)]
	        [(and old (vector? range)) (random-from-vec-ex range old)]
	        [(vector? range) (random-from-vec range)]
	        [else #f]))

	    ;; Create random operands from opcode.  ARM immediates are semantic
	    ;; values here; ISA pattern restrictions remain the final instruction
	    ;; word filter in random-instruction.
	    (define (random-instruction
	             index n live-in
	             [opcode-id #f]
	             [tries 0])
	      (when (> tries 1000)
	        (raise "random-instruction: cannot find an instruction allowed by the current ISA restrictions"))
	      (unless opcode-id
	        (define opcode-pool
	          (send machine get-valid-opcode-pool index n live-in))
	        (unless (nonempty-list? opcode-pool)
	          (raise "random-instruction: no opcode allowed by the current live-in state"))
	        (set! opcode-id (random-from-list (prefer-flag-opcodes opcode-pool))))
	      (define args (random-args-from-op opcode-id live-in))
	      (define candidate (and args (inst opcode-id args)))
	      (if (and candidate (send machine inst-allowed? candidate))
	          candidate
	          (random-instruction index n live-in #f (add1 tries))))

	    (define (random-args-from-op opcode-id live-in)
	      (define types (send machine get-arg-types opcode-id))
	      (define ranges (send machine get-arg-ranges opcode-id #f live-in))
	      (when debug (pretty-display (format " --> ranges ~a" ranges)))
	      (define pass (and ranges (for/and ([range ranges]) (> (vector-length range) 0))))
	      (and pass
	           (for/vector ([range ranges] [type types])
	                       (random-value-for-type type range))))


    ;; Mutate opcode.
    ;; index: index to be mutated
    ;; entry: instruction at index in p
    ;; p: entire program
    (define/override (mutate-opcode index entry p)
      (define opcode-id (inst-op entry))
      (define opcode-name (send machine get-opcode-name opcode-id))
      (define op-types
        (filter identity (for/list ([op opcode-id] [index (in-naturals)]) (and (>= op 0) index))))
      (define op-type (random-from-list op-types))
      (define checks (remove op-type (range (vector-length opcode-id))))
      (define class
        (prefer-flag-opcodes
         (filter
          (lambda (x) (for/and ([index checks]) (= (vector-ref x index) (vector-ref opcode-id index))))
          (send machine get-class-opcodes opcode-id))))
      (when debug
            (pretty-display (format " >> mutate opcode"))
            (pretty-display (format " --> org = ~a ~a" opcode-name opcode-id))
            (pretty-display (format " --> op-type = ~a" op-type))
            (pretty-display (format " --> class = ~a" class)))
      (cond
       [(nonempty-list? class)
        (define new-opcode-id (random-from-list-ex class opcode-id))
        (define new-p (vector-copy p))
        (when debug
              (pretty-display (format " --> new = ~a ~a" (send machine get-opcode-name new-opcode-id) new-opcode-id)))
        (vector-set! new-p index (inst-copy-with-op entry new-opcode-id))
        (send stat inc-propose `opcode)
        new-p]

	       [else (mutate p)]))

	    ;; Mutate operand.  This mirrors the generic stochastic mutator, but
	    ;; lets ARM immediates draw from their broader semantic domains instead
	    ;; of only from the current finite argument-range vector.
	    (define (mutate-operand index entry p)
	      (define opcode-id (inst-op entry))
	      (define opcode-name (send machine get-opcode-name opcode-id))
	      (define args (vector-copy (inst-args entry)))
	      (define my-live-in live-in)
	      (for ([i index])
	           (set! my-live-in (send machine update-live my-live-in (vector-ref p i))))
	      (define types (send machine get-arg-types opcode-id))
	      (define ranges (send machine get-arg-ranges opcode-id entry my-live-in))
	      (cond
	       [(and ranges (> (vector-length ranges) 0))
	        (define okay-indexes (list))
	        (for ([range ranges]
	              [type types]
	              [i (vector-length ranges)])
	             (when (or (equal? type 'const)
	                       (equal? type 'bit)
	                       (> (vector-length range) 1))
	                   (set! okay-indexes (cons i okay-indexes))))
	        (cond
	         [(empty? okay-indexes) (mutate p)]
	         [else
	          (define change (random-from-list okay-indexes))
	          (define valid-vals (vector-ref ranges change))
	          (define type (vector-ref types change))
	          (define new-val
	            (random-value-for-type type valid-vals (vector-ref args change)))
	          (define new-p (vector-copy p))
	          (when debug
	                (pretty-display (format " --> org = ~a ~a" opcode-name args))
	                (pretty-display (format " --> choices = ~a" valid-vals))
	                (pretty-display (format " --> new = [~a]->~a" change new-val)))
	          (vector-set! args change new-val)
	          (vector-set! new-p index (inst-copy-with-args entry args))
	          (send stat inc-propose `operand)
	          new-p])]
	       [else (mutate p)]))


	    (define (diff-cost x y)
      (pop-count32 (bitwise-xor (bitwise-and x #xffffffff) 
                                (bitwise-and y #xffffffff))))
    
    ;; Compute correctness cost sum of all bit difference in live variables.
    ;; state1: expected in progstate format
    ;; state2: actual in progstate format
    (define (correctness-cost state1 state2 constraint)
      (define expected-memory (progstate-memory state1))
      (define actual-memory (progstate-memory state2))
      (define memory-constraint (progstate-memory constraint))
      (+ (correctness-cost-base (progstate-regs state1)
                                (progstate-regs state2)
                                (progstate-regs constraint)
                                diff-cost)
         (if (and (is-a? expected-memory memory-racket%)
                  (is-a? actual-memory memory-racket%)
                  (or memory-constraint
                      (send expected-memory get-live-mask)))
             (send expected-memory correctness-cost
                   actual-memory diff-cost bit)
             0)
         (flag-bit-cost (progstate-n state1) (progstate-n state2) (progstate-n constraint))
         (flag-bit-cost (progstate-zf state1) (progstate-zf state2) (progstate-zf constraint))
         (flag-bit-cost (progstate-c state1) (progstate-c state2) (progstate-c constraint))
         (flag-bit-cost (progstate-v state1) (progstate-v state2) (progstate-v constraint))))
    ))




  
