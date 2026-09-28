#lang racket

(require "../parallel-driver.rkt" "../inst.rkt"
         "../solver-config.rkt"
         "arm-parser.rkt" "arm-machine.rkt" 
         "arm-printer.rkt"
	 ;; simulator, validator
	 "arm-simulator-racket.rkt" 
	 "arm-simulator-rosette.rkt"
         "arm-validator.rkt")

(provide optimize)

(define (parse-reg-id value)
  (and (string? value)
       (regexp-match? #rx"^r[0-9]+$" value)
       (string->number (substring value 1))))

(define (parse-number value)
  (cond
   [(number? value) value]
   [(string? value) (string->number value)]
   [else #f]))

(define (stack-scratch-offset? offset stack-size direction)
  (and offset
       (cond
        [(equal? direction 'downwards) (and (< offset 0) (<= (- offset) stack-size))]
        [(equal? direction 'upwards) (and (> offset 0) (<= offset stack-size))]
        [else #f])))

(define (stack-scratch-only-store? my-inst stack-scratch-config)
  (and stack-scratch-config
       (let* ([op (vector-ref (inst-op my-inst) 0)]
              [args (inst-args my-inst)])
         (and (member op '("str" "strb" "strh" "str-full" "strb-full" "strh-full"))
              (or (= (vector-length args) 3)
                  (and (= (vector-length args) 6)
                       (equal? (vector-ref args 3) "1")
                       (equal? (vector-ref args 5) "0")))
              (let* ([base-reg (parse-reg-id (vector-ref args 1))]
                     [raw-offset (parse-number (vector-ref args 2))]
                     [up? (or (= (vector-length args) 3)
                              (equal? (vector-ref args 4) "1"))]
                     [offset (and raw-offset (if up? raw-offset (- raw-offset)))]
                    [sp-reg (list-ref stack-scratch-config 0)]
                    [stack-size (list-ref stack-scratch-config 1)]
                    [direction (list-ref stack-scratch-config 2)])
                (and base-reg
                     (= base-reg sp-reg)
                     (stack-scratch-offset? offset stack-size direction)))))))

(define (memory-writing-inst? my-inst stack-scratch-config)
  (define op (vector-ref (inst-op my-inst) 0))
  (cond
   [(member op '("str" "strb" "strh" "str-full" "strb-full" "strh-full"))
    (not (stack-scratch-only-store? my-inst stack-scratch-config))]
   [(member op '("stm" "stm-full" "swp" "swpb")) #t]
   [else #f]))

(define (augment-live-out code live-out stack-scratch-config)
  (if (or (member 'memory live-out)
          (not (for/or ([my-inst code])
                 (memory-writing-inst? my-inst stack-scratch-config))))
      live-out
      (append live-out '(memory))))

;; Main function to perform superoptimization on multiple cores.
;; >>> INPUT >>>
;; code: program to superoptimized in string-IR format
;; >>> OUTPUT >>>
;; Optimized code in string-IR format
(define (optimize code live-out search-type mode
                  #:dir [dir "output"] 
                  #:cores [cores 4]
                  #:time-limit [time-limit 3600]
                  #:size [size #f]
                  #:window [window #f]
                  #:input-file [input-file #f]
                  #:restriction-file [restriction-file #f]
                  #:solver-name [solver-name 'kodkod]
                  #:stack-scratch-config [stack-scratch-config #f]
                  #:min-scratch-regs [min-scratch-regs 1]
                  #:post-correct-time [post-correct-time #f]
                  #:post-correct-remaining-frac [post-correct-remaining-frac #f]
                  #:performance-cost-syn [performance-cost-syn 1]
                  #:performance-cost-opt [performance-cost-opt 5])
  (define normalized-solver-name (normalize-solver-name solver-name))
  (define normalized-restriction-file
    (and restriction-file
         (path->string (simplify-path (path->complete-path restriction-file)))))
  (define parser (new arm-parser%))
  (define machine (new arm-machine%))
  (send machine set-min-scratch-regs! min-scratch-regs)
  (when stack-scratch-config
        (send machine set-stack-scratch-config!
              (list-ref stack-scratch-config 0)
              (list-ref stack-scratch-config 1)
              (list-ref stack-scratch-config 2)))
  (when normalized-restriction-file
        (send machine load-restrictions! normalized-restriction-file))
  (define effective-live-out
    (augment-live-out code live-out stack-scratch-config))
  (define printer (new arm-printer% [machine machine]))
  (define simulator (new arm-simulator-rosette% [machine machine]))
  (define validator (new arm-validator% [machine machine] [simulator simulator]
                         [solver-name normalized-solver-name]))
  (define parallel (new parallel-driver% [isa "arm"] [parser parser] [machine machine] 
                        [printer printer] [validator validator]
                        [search-type search-type] [mode mode]
                        [window window]
                        [restriction-file normalized-restriction-file]
                        [solver-name normalized-solver-name]
                        [performance-cost-syn performance-cost-syn]
                        [performance-cost-opt performance-cost-opt]))

  (send parallel optimize code effective-live-out 
        #:dir dir #:cores cores 
        #:time-limit time-limit #:size size #:input-file input-file
        #:post-correct-time post-correct-time
        #:post-correct-remaining-frac post-correct-remaining-frac)
  )
  
;; (define (arm-generate-inputs code machine-config dir)
;;   (define machine (new arm-machine% [config machine-config]))
;;   (define printer (new arm-printer% [machine machine]))
;;   (define simulator (new arm-simulator-rosette% [machine machine]))
;;   (define validator (new arm-validator% [machine machine] [simulator simulator]))
;;   (generate-inputs (send printer encode code) #f dir machine printer validator))
