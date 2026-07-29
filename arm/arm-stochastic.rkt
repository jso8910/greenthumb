#lang racket

(require "../stochastic.rkt"
         "../inst.rkt"
         "../machine.rkt" "arm-machine.rkt")

(provide arm-stochastic%)

(define arm-stochastic%
	  (class stochastic%
	    (super-new)
	    (inherit-field machine stat mutate-dist live-in)
	    (inherit mutate pop-count32 correctness-cost-base
	             inst-copy-with-op inst-copy-with-args)
	    (override correctness-cost 
	              random-args-from-op mutate-operand
	              )
    (set! mutate-dist
          #hash((opcode . 2) (operand . 1) (swap . 1) (instruction . 1)))
	  

	    (define bit (get-field bitwidth machine))

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
	    (define (random-args-from-op opcode-id live-in)
	      (define ranges (send machine get-arg-ranges opcode-id #f live-in))
	      (define types (send machine get-arg-types opcode-id))
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
        (filter
         (lambda (x) (for/and ([index checks]) (= (vector-ref x index) (vector-ref opcode-id index))))
        (send machine get-class-opcodes opcode-id)))
      (when debug
            (pretty-display (format " >> mutate opcode"))
            (pretty-display (format " --> org = ~a ~a" opcode-name opcode-id))
            (pretty-display (format " --> op-type = ~a" op-type))
            (pretty-display (format " --> class = ~a" class)))
      (cond
       [class
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
	      (define ranges (send machine get-arg-ranges opcode-id entry my-live-in))
	      (define types (send machine get-arg-types opcode-id))
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
      (+ (correctness-cost-base (progstate-regs state1)
                                (progstate-regs state2)
                                (progstate-regs constraint)
                                diff-cost)
         (if (progstate-memory constraint)
             (send (progstate-memory state1) correctness-cost
                   (progstate-memory state2) diff-cost bit)
             0)
         (if (and (progstate-z constraint)
                  (not (equal? (progstate-z state1) (progstate-z state2))))
             1
             0)))
    ))




  
