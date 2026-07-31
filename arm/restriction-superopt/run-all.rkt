#lang racket

(require racket/cmdline
         racket/file
         racket/list
         racket/match
         racket/runtime-path
         "../../inst.rkt"
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-simulator-racket.rkt")

(define-runtime-path script-dir ".")
(define greenthumb-root (simplify-path (build-path script-dir "../..")))
(define optimizer-path (build-path greenthumb-root "arm/optimize.rkt"))
(define racket-executable (find-executable-path "racket"))
(define pgrep-executable (find-executable-path "pgrep"))
(define kill-executable (find-executable-path "kill"))

(unless racket-executable
  (raise-user-error 'run-all "could not find racket executable on PATH"))

(define (greenthumb-relative-string path)
  (path->string (find-relative-path greenthumb-root path)))

(define (subprocess-output executable . args)
  (define-values (sp stdout stdin stderr)
    (apply subprocess #f #f #f executable args))
  (close-output-port stdin)
  (define out (port->string stdout))
  (close-input-port stdout)
  (subprocess-wait sp)
  (if (equal? (subprocess-status sp) 0)
      out
      ""))

(define (child-pids pid)
  (if pgrep-executable
      (filter number?
              (map string->number
                   (string-split
                    (subprocess-output pgrep-executable "-P" (number->string pid)))))
      '()))

(define (kill-process-tree pid)
  (for ([child (child-pids pid)])
    (kill-process-tree child))
  (when kill-executable
    (with-handlers ([exn? void])
      (system* kill-executable "-TERM" (number->string pid)))))

(define (run-optimizer args)
  (define-values (sp stdout stdin stderr)
    (parameterize ([current-directory greenthumb-root])
      (apply subprocess
             (current-output-port)
             #f
             (current-error-port)
             racket-executable
             args)))
  (with-handlers
    ([exn:break?
      (lambda (e)
        (printf "\nInterrupted; stopping optimizer workers...\n")
        (flush-output)
        (kill-process-tree (subprocess-pid sp))
        (subprocess-kill sp #t)
        (subprocess-wait sp)
        (raise e))])
    (subprocess-wait sp)
    (equal? (subprocess-status sp) 0)))

(define include-hard? (make-parameter #f))
(define timeout-seconds (make-parameter #f))
(define candidate-size (make-parameter #f))
(define workers (make-parameter 4))
(define post-correct-time (make-parameter 20))
(define post-correct-remaining-frac (make-parameter 1/4))
(define output-root
  (make-parameter (build-path greenthumb-root "arm/restriction-superopt/output")))
(define generated-root
  (make-parameter (build-path greenthumb-root "arm/restriction-superopt/generated")))

(define (parse-nonnegative-number who value)
  (define parsed (string->number value))
  (unless (and (number? parsed) (>= parsed 0))
          (raise-user-error who "expected a non-negative number, got ~a" value))
  parsed)

(command-line
 #:program "run-all.rkt"
 #:once-each
 [("--include-hard") "Run cases marked hard in expected.rkt." (include-hard? #t)]
 [("-t" "--timeout") seconds "Override per-case timeout." (timeout-seconds (string->number seconds))]
 [("-n" "--size") size "Override per-case candidate size." (candidate-size (string->number size))]
 [("-c" "--workers") count "Worker count; values below 4 are rejected." (workers (string->number count))]
 [("--no-two-phase-stop") "Disable post-correct early stopping." (post-correct-time #f) (post-correct-remaining-frac #f)]
 [("--post-correct-time") seconds "Seconds to keep improving after the first correct program." (post-correct-time (parse-nonnegative-number 'post-correct-time seconds))]
 [("--post-correct-remaining-frac" "--post-correct-frac") frac "Fraction of remaining timeout to keep improving after the first correct program." (post-correct-remaining-frac (parse-nonnegative-number 'post-correct-remaining-frac frac))]
 [("-o" "--output-root") dir "GreenThumb optimizer output root." (output-root dir)]
 [("--generated-root") dir "Generated case root." (generated-root dir)])

(when (< (workers) 4)
  (raise-user-error 'run-all "restriction superopt tests require at least 4 workers"))

(define (metadata-ref metadata key [default #f])
  (define found (assoc key metadata))
  (if found (second found) default))

(struct case-result
  (name status elapsed-seconds optimizer-ok? best-cost best-len best-time
        best-observed-cost best-correct-cost iterations output-dir message)
  #:transparent)

(define (case-directories)
  (sort
   (filter directory-exists? (directory-list (generated-root) #:build? #t))
   string<?
   #:key path->string))

(define (read-metadata case-dir)
  (call-with-input-file (build-path case-dir "expected.rkt") read))

(define (read-best-info output-dir)
  (define info-file (build-path output-dir "best.info"))
  (if (file-exists? info-file)
      (with-handlers ([exn? (lambda (e) (values #f #f #f))])
        (call-with-input-file info-file
          (lambda (in)
            (define cost (string->number (read-line in)))
            (define len (string->number (read-line in)))
            (define best-time (read-line in))
            (values cost len best-time))))
      (values #f #f #f)))

(define (parse-stat-file file)
  (with-handlers ([exn? (lambda (e) (hash))])
    (call-with-input-file file
      (lambda (in)
        (let loop ([stats (hash)])
          (define line (read-line in))
          (if (eof-object? line)
              stats
              (let ([tokens (string-split line)])
                (loop
                 (if (< (length tokens) 2)
                     stats
                     (let ([key (string->symbol (string-trim (first tokens) ":"))]
                           [value (string->number (second tokens))])
                       (if value
                           (hash-set stats key value)
                           stats)))))))))))

(define (read-worker-stats output-dir)
  (define stat-files
    (if (directory-exists? output-dir)
        (find-files (lambda (path)
                      (regexp-match? #rx"[.]stat$" (path->string path)))
                    output-dir)
        '()))
  (define parsed (map parse-stat-file stat-files))
  (define (values-for key)
    (filter number? (map (lambda (stats) (hash-ref stats key #f)) parsed)))
  (define (min-or-false xs) (and (not (empty? xs)) (apply min xs)))
  (define (sum xs) (foldl + 0 xs))
  (values (min-or-false (values-for 'best-cost))
          (min-or-false (values-for 'best-correct-cost))
          (sum (values-for 'iterations))))

(define cond-suffix-rx "(eq|ne|cs|cc|mi|pl|vs|vc|hi|ls|ge|lt|gt|le|al)?")

(define branch-op-rx
  (pregexp (format "^\\s*(b|bl|bx)~a(\\s|$)" cond-suffix-rx)))

(define (assert-no-branches! file)
  (for ([line (file->lines file)]
        [line-number (in-naturals 1)])
    (when (regexp-match? branch-op-rx line)
      (raise-user-error 'run-all
                        "branch instruction in ~a on line ~a: ~a"
                        file
                        line-number
                        line))))

(define (assert-program-allowed! best-file restrict-file)
  (define machine (new arm-machine% [config 16]))
  (define parser (new arm-parser%))
  (define printer (new arm-printer% [machine machine]))
  (send machine load-restrictions! restrict-file)
  (define program (send printer encode (send parser ir-from-file best-file)))
  (unless (send machine program-allowed? program)
    (raise-user-error 'run-all
                      "optimized program violates restrictions: ~a"
                      best-file)))

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

(define (stack-scratch-only-store? my-inst stack-scratch)
  (and stack-scratch
       (let* ([op (vector-ref (inst-op my-inst) 0)]
              [args (inst-args my-inst)])
         (and (member op '("str" "strb" "strh"))
              (= (vector-length args) 3)
              (let ([base-reg (parse-reg-id (vector-ref args 1))]
                    [offset (parse-number (vector-ref args 2))]
                    [sp-reg (first stack-scratch)]
                    [stack-size (second stack-scratch)]
                    [direction (third stack-scratch)])
                (and base-reg
                     (= base-reg sp-reg)
                     (stack-scratch-offset? offset stack-size direction)))))))

(define (memory-writing-inst? my-inst stack-scratch)
  (define op (vector-ref (inst-op my-inst) 0))
  (cond
    [(member op '("str" "strb" "strh"))
     (not (stack-scratch-only-store? my-inst stack-scratch))]
    [(member op '("stm" "swp" "swpb")) #t]
    [else #f]))

(define (augment-live-out code live-out stack-scratch)
  (if (or (member 'memory live-out)
          (not (for/or ([my-inst code])
                 (memory-writing-inst? my-inst stack-scratch))))
      live-out
      (append live-out '(memory))))

(define concrete-reg-samples
  (list
   '#(0 5 3 1 4 7 11 13 17 19 23 29 4096 37 41 45)
   '#(0 -7 11 2 -1 0 32 255 256 1024 -1024 3 8192 5 6 7)
   '#(0 2147483647 1 31 2 4 8 16 32 64 128 256 12288 512 1024 2048)
   '#(0 -2147483648 -1 8 15 16 23 42 99 100 101 102 16384 103 104 105)))

(define (const-init value)
  (lambda (#:min [min #f] #:max [max #f] #:const [const #f])
    (cond
      [const const]
      [else value])))

(define (state-from-regs machine regs flags)
  (define state (send machine get-state (const-init 0)))
  (set-progstate-regs! state (vector-copy regs))
  (set-progstate-z! state flags)
  state)

(define (set-stack-scratch-if-present! machine stack-scratch)
  (when stack-scratch
    (send machine set-stack-scratch-config!
          (first stack-scratch)
          (second stack-scratch)
          (third stack-scratch))))

(define (assert-semantics! input-file best-file info-file stack-scratch)
  (define machine (new arm-machine% [config 16]))
  (set-stack-scratch-if-present! machine stack-scratch)
  (define parser (new arm-parser%))
  (define printer (new arm-printer% [machine machine]))
  (define simulator (new arm-simulator-racket% [machine machine]))
  (define original-source (send parser ir-from-file input-file))
  (define live-out-source (send parser info-from-file info-file))
  (define original (send printer encode original-source))
  (define candidate (send printer encode (send parser ir-from-file best-file)))
  (define constraint
    (send printer encode-live
          (augment-live-out original-source live-out-source stack-scratch)))
  (for* ([regs concrete-reg-samples]
         [flags '(0 2 4 8 15)])
    (define input-state (state-from-regs machine regs flags))
    (define original-output (send simulator interpret original input-state))
    (define candidate-output (send simulator interpret candidate input-state))
    (unless (send machine state-eq? original-output candidate-output constraint)
      (raise-user-error 'run-all
                        "concrete semantic mismatch for ~a with flags ~a and regs ~a"
                        best-file
                        flags
                        regs))))

(define (contains-any-opcode? file opcodes)
  (define lines (file->lines file))
  (for/or ([opcode opcodes])
    (define rx (pregexp (format "^\\s*~a~a(\\s|,|$)"
                                (regexp-quote opcode)
                                cond-suffix-rx)))
    (for/or ([line lines]) (regexp-match? rx line))))

(define (assert-forbidden-opcodes! best-file metadata)
  (define forbidden-opcodes (metadata-ref metadata 'forbidden-opcodes '()))
  (for ([opcode forbidden-opcodes])
    (when (contains-any-opcode? best-file (list opcode))
      (raise-user-error 'run-all
                        "optimized program contains forbidden opcode ~a in ~a"
                        opcode
                        best-file))))

(define (run-case case-dir)
  (define metadata (read-metadata case-dir))
  (define hard? (metadata-ref metadata 'hard #f))
  (define name (metadata-ref metadata 'name (path->string (file-name-from-path case-dir))))
  (define started-at (current-seconds))
  (define (finish status optimizer-ok? case-output message)
    (define-values (best-cost best-len best-time)
      (if case-output
          (read-best-info case-output)
          (values #f #f #f)))
    (define-values (best-observed-cost best-correct-cost iterations)
      (if case-output
          (read-worker-stats case-output)
          (values #f #f 0)))
    (case-result name
                 status
                 (- (current-seconds) started-at)
                 optimizer-ok?
                 best-cost
                 best-len
                 best-time
                 best-observed-cost
                 best-correct-cost
                 iterations
                 case-output
                 message))
  (cond
    [(and hard? (not (include-hard?)))
     (printf "SKIP hard case ~a\n" name)
     (finish 'skip #f #f "hard case skipped")]
    [else
     (let* ([case-output (build-path (output-root) name)]
            [timeout (or (timeout-seconds) (metadata-ref metadata 'timeout 60))]
            [size (or (candidate-size) (metadata-ref metadata 'size 3))]
            [stack-scratch (metadata-ref metadata 'stack-scratch #f)]
            [optimizer-file (greenthumb-relative-string optimizer-path)]
            [case-output-arg (greenthumb-relative-string case-output)]
            [restrict-file-arg
             (greenthumb-relative-string (build-path case-dir "restrict.rkt"))]
            [input-file-arg
             (greenthumb-relative-string (build-path case-dir "input.s"))]
            [post-correct-args
             (append
              (if (post-correct-time)
                  (list "--post-correct-time" (format "~a" (post-correct-time)))
                  '())
              (if (post-correct-remaining-frac)
                  (list "--post-correct-remaining-frac" (format "~a" (post-correct-remaining-frac)))
                  '()))]
            [stack-args
             (match stack-scratch
               [(list reg bytes direction)
                (list "--stack-pointer-reg" (format "~a" reg)
                      "--stack-scratch-size" (format "~a" bytes)
                      "--stack-direction" (symbol->string direction))]
               [_ '()])]
            [args
             (append
              (list optimizer-file
                    "--stoch" "-s" "--solver" "z3"
                    "-c" (number->string (workers))
                    "-t" (number->string timeout)
                    "-n" (number->string size)
                    "-d" case-output-arg
                    "--restrict" restrict-file-arg)
              post-correct-args
              stack-args
              (list input-file-arg))])
       (with-handlers
         ([exn?
           (lambda (e)
             (printf "FAIL ~a: ~a\n" name (exn-message e))
             (finish 'fail #f case-output (exn-message e)))])
         (make-directory* case-output)
         (printf "RUN ~a\n" name)
         (flush-output)
         (let ([ok?
                (run-optimizer args)])
           (cond
             [(not ok?)
              (printf "FAIL ~a: optimizer failed or timed out\n" name)
              (finish 'fail #f case-output "optimizer failed or timed out")]
             [else
              (let ([best-file (build-path case-output "best.s")])
                (unless (file-exists? best-file)
                  (raise-user-error 'run-all "optimizer produced no best.s for case ~a" name))
                (assert-no-branches! best-file)
                (assert-program-allowed! best-file (build-path case-dir "restrict.rkt"))
                (assert-forbidden-opcodes! best-file metadata)
                (assert-semantics! (build-path case-dir "input.s")
                                   best-file
                                   (build-path case-dir "input.s.info")
                                   stack-scratch)
                (printf "PASS ~a\n" name)
                (finish 'pass #t case-output "ok"))]))))]))

(define (display-cell value)
  (cond
    [(path? value) (path->string value)]
    [(not value) "-"]
    [else (format "~a" value)]))

(define (print-result result)
  (printf "~a\t~a\t~as\tbest-cost=~a\tlen=~a\tbest-time=~a\tseen-cost=~a\tseen-correct=~a\titers=~a\t~a\n"
          (case-result-status result)
          (case-result-name result)
          (case-result-elapsed-seconds result)
          (display-cell (case-result-best-cost result))
          (display-cell (case-result-best-len result))
          (display-cell (case-result-best-time result))
          (display-cell (case-result-best-observed-cost result))
          (display-cell (case-result-best-correct-cost result))
          (display-cell (case-result-iterations result))
          (case-result-message result)))

(define (count-status results status)
  (length (filter (lambda (result) (equal? (case-result-status result) status))
                  results)))

(define results
  (for/list ([case-dir (case-directories)])
    (run-case case-dir)))

(newline)
(printf "RESULTS\n")
(printf "-------\n")
(for ([result results])
  (print-result result))
(newline)
(printf "SUMMARY\n")
(printf "-------\n")
(printf "total:\t~a\n" (length results))
(printf "pass:\t~a\n" (count-status results 'pass))
(printf "fail:\t~a\n" (count-status results 'fail))
(printf "skip:\t~a\n" (count-status results 'skip))
