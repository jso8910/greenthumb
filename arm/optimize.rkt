#lang racket

(require "arm-parser.rkt"
         "arm-machine.rkt"
         "arm-printer.rkt"
         "main.rkt"
         racket/file)

(define size (make-parameter #f))
(define cores (make-parameter 6))
(define search-type (make-parameter `hybrid))
(define mode (make-parameter `syn))

(define dir (make-parameter "output"))
(define time-limit (make-parameter 3600))
(define input-file (make-parameter #f))
(define window (make-parameter #f))
(define restriction-file (make-parameter #f))
(define solver-name (make-parameter 'kodkod))
(define stack-pointer-reg (make-parameter #f))
(define stack-scratch-size (make-parameter #f))
(define stack-direction (make-parameter #f))
(define post-correct-time (make-parameter #f))
(define post-correct-remaining-frac (make-parameter #f))

(define (parse-nonnegative-integer who value)
  (define parsed (string->number value))
  (unless (and (integer? parsed) (>= parsed 0))
          (raise-user-error who "expected a non-negative integer, got ~a" value))
  parsed)

(define (parse-positive-integer who value)
  (define parsed (string->number value))
  (unless (and (integer? parsed) (> parsed 0))
          (raise-user-error who "expected a positive integer, got ~a" value))
  parsed)

(define (parse-nonnegative-number who value)
  (define parsed (string->number value))
  (unless (and (number? parsed) (>= parsed 0))
          (raise-user-error who "expected a non-negative number, got ~a" value))
  parsed)

(define (parse-stack-pointer-reg value)
  (define normalized (string-downcase value))
  (cond
   [(regexp-match #rx"^r[0-9]+$" normalized)
    (parse-nonnegative-integer 'stack-pointer-reg (substring normalized 1))]
   [else (parse-nonnegative-integer 'stack-pointer-reg normalized)]))

(define (parse-stack-direction value)
  (define normalized (string->symbol (string-downcase value)))
  (cond
   [(member normalized '(up upwards upward)) 'upwards]
   [(member normalized '(down downwards downward)) 'downwards]
   [else
    (raise-user-error
     'stack-direction
     "expected upwards/downwards, got ~a"
     value)]))

(define (selected-stack-scratch-config)
  (define sp-reg (stack-pointer-reg))
  (define size (stack-scratch-size))
  (define direction (stack-direction))
  (cond
   [(and sp-reg size direction) (list sp-reg size direction)]
   [(or sp-reg size direction)
    (raise-user-error
     'arm-optimize
     "stack scratch requires --stack-pointer-reg, --stack-scratch-size, and --stack-direction")]
   [else #f]))
 
(define file-to-optimize
  (command-line
   #:once-each
   [("-c" "--core")      c
                        "Number of search instances (default=8)"
                        (cores (string->number c))]
   [("-d" "--dir")      d
                        "Output directory (default=output)"
                        (dir d)]
   [("-t" "--time-limit") t
                        "Time limit in seconds (default=3600)."
                        (time-limit t)]
   [("--two-phase-stop")
                        "After the first validated correct program, keep searching for min(20s, 25% of remaining time)."
                        (post-correct-time 20)
                        (post-correct-remaining-frac 1/4)]
   [("--post-correct-time") t
                        "Two-phase stop: max seconds to keep improving after the first validated correct program."
                        (post-correct-time (parse-nonnegative-number 'post-correct-time t))]
   [("--post-correct-remaining-frac" "--post-correct-frac") f
                        "Two-phase stop: max fraction of the remaining timeout to keep improving after the first validated correct program."
                        (post-correct-remaining-frac (parse-nonnegative-number 'post-correct-remaining-frac f))]
   [("-n" "--size")     n
                        "Code size limit. (default=#f)."
                        (size n)]
   [("-i" "--input")    i
                        "Path to inputs. (default=#f)."
                        (input-file i)]
   [("-r" "--restrict") r
                        "Path to ARM32 ISA restriction file. (default=#f)."
                        (restriction-file r)]
   [("--solver") s
                        "Solver backend: kodkod or z3. (default=kodkod)."
                        (solver-name (string->symbol s))]
   [("--stack-pointer-reg" "--sp-reg") r
                        "Stack pointer register for scratch memory, e.g. r12 or 12."
                        (stack-pointer-reg (parse-stack-pointer-reg r))]
   [("--stack-scratch-size" "--stack-size") n
                        "Number of SP-relative scratch bytes available to candidates."
                        (stack-scratch-size (parse-positive-integer 'stack-scratch-size n))]
   [("--stack-direction") d
                        "Stack scratch direction: upwards/up or downwards/down."
                        (stack-direction (parse-stack-direction d))]
   [("-w" "--window")    w
                        "Window size."
                        (window (string->number w))]
   #:once-any
   [("--sym") "Use symbolic search."
                        (search-type `solver)]
   [("--stoch") "Use stochastic search."
                        (search-type `stoch)]
   [("--enum") "Use enumerative search."
                        (search-type `enum)]
   [("--hybrid") "Use stochastic search."
                        (search-type `hybrid)]

   #:once-any
   [("-l" "--linear")   "Linear search."
                        (mode `linear)]
   [("-b" "--binary")   "Binary search."
                        (mode `binary)]
   [("-p" "--partial")   "Partial search."
                        (mode `partial)]

   #:once-any
   [("-o" "--optimize") "Optimize mode starts searching from the original program"
                        (mode `opt)]
   [("-s" "--synthesize") "Synthesize mode starts searching from random programs (default)"
                        (mode `syn)]

   #:args (filename) ; expect one command-line argument: <filename>
   ; return the argument as a filename to compile
   filename))

(define parser (new arm-parser%))
(define stack-scratch-config (selected-stack-scratch-config))
(define code (send parser ir-from-file file-to-optimize))
(define live-out (send parser info-from-file (string-append file-to-optimize ".info")))

(define optimized-code
  (optimize code
            live-out
            (search-type) (mode)
            #:dir (dir) #:cores (cores) 
            #:time-limit (time-limit) #:size (size) #:window (window)
            #:input-file (input-file)
            #:restriction-file (restriction-file)
            #:solver-name (solver-name)
            #:stack-scratch-config stack-scratch-config
            #:post-correct-time (post-correct-time)
            #:post-correct-remaining-frac (post-correct-remaining-frac)))

(make-directory* (dir))
(with-output-to-file #:exists 'truncate (build-path (dir) "best.s")
  (lambda ()
    (define machine (new arm-machine%))
    (define printer (new arm-printer% [machine machine]))
    (send printer print-syntax optimized-code)))
