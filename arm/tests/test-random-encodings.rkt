#lang racket

(require racket/cmdline
         racket/file
         racket/format
         racket/list
         racket/match
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-restrictions.rkt")

(struct sample (gt-asm as-asm kind) #:transparent)

(define count 200)
(define seed #f)
(define assembler #f)
(define objcopy #f)
(define arch "armv7ve")
(define verbose? #f)
(define progress-interval 1000)

(command-line
 #:program "test-random-encodings.rkt"
 #:once-each
 [("-n" "--count") n "Number of random instructions to check"
                   (set! count (string->number n))]
 [("--seed") n "Random seed"
             (set! seed (string->number n))]
 [("--as") path "ARM assembler executable"
         (set! assembler path)]
 [("--objcopy") path "objcopy executable"
                (set! objcopy path)]
 [("--arch") value "GNU as -march value"
            (set! arch value)]
 [("--verbose") "Print each checked instruction"
                (set! verbose? #t)]
 [("--progress") n "Print progress every n samples; 0 disables progress"
                 (set! progress-interval (string->number n))])

(unless (and (exact-nonnegative-integer? count) (> count 0))
  (raise-user-error 'test-random-encodings "count must be a positive integer, got ~s" count))
(unless (exact-nonnegative-integer? progress-interval)
  (raise-user-error 'test-random-encodings
                    "progress interval must be a nonnegative integer, got ~s"
                    progress-interval))
(when seed
  (unless (exact-nonnegative-integer? seed)
    (raise-user-error 'test-random-encodings "seed must be a nonnegative integer, got ~s" seed))
  (random-seed seed))

(define (find-tool names)
  (for/or ([name names])
    (find-executable-path name)))

(define as-path
  (or assembler
      (find-tool '("arm-none-eabi-as"
                   "arm-linux-gnueabi-as"
                   "arm-linux-gnueabihf-as"))))
(define objcopy-path
  (or objcopy
      (find-tool '("arm-none-eabi-objcopy"
                   "arm-linux-gnueabi-objcopy"
                   "arm-linux-gnueabihf-objcopy"
                   "llvm-objcopy"
                   "objcopy"))))

(unless as-path
  (raise-user-error 'test-random-encodings
                    "could not find an ARM assembler; pass --as /path/to/arm-none-eabi-as"))
(unless objcopy-path
  (raise-user-error 'test-random-encodings
                    "could not find objcopy; pass --objcopy /path/to/objcopy"))

(define parser (new arm-parser%))
(define machine (new arm-machine% [config 8]))
(define printer (new arm-printer% [machine machine]))

(define conds '("" "eq" "ne" "cs" "cc" "mi" "pl" "vs" "vc" "hi" "ls" "ge" "lt" "gt" "le"))
(define regs (for/list ([i (in-range 15)]) (format "r~a" i)))
(define imm8s '(0 1 2 3 4 7 8 15 16 31 32 63 64 127 128 255))
(define imm16s '(0 1 2 255 256 1024 4095 4096 32768 65535))
(define shift-amounts '(0 1 2 3 4 7 8 15 16 31))
(define nonzero-shift-amounts '(1 2 3 4 7 8 15 16 31))
(define shift-ops '("lsl" "lsr" "asr" "ror"))

(define (pick xs) (list-ref xs (random (length xs))))
(define (r) (pick regs))
(define (cond-suffix) (pick conds))
(define (op op-name) (format "~a~a" op-name (cond-suffix)))
(define (imm xs) (format "#~a" (pick xs)))
(define (asm-line mnemonic args)
  (format "~a ~a\n" mnemonic (string-join args ", ")))

(define (signed-imm amount)
  (define sign (if (or (= amount 0) (zero? (random 2))) "" "-"))
  (format "#~a~a" sign amount))

(define (shift-imm shf)
  (cond
    [(equal? shf "lsl") (imm shift-amounts)]
    [else (imm nonzero-shift-amounts)]))

(define (distinct-regs n)
  (let loop ([out '()])
    (if (= (length out) n)
        out
        (let ([next (r)])
          (if (member next out)
              (loop out)
              (loop (cons next out)))))))

(define (bitfield-width lsb)
  (add1 (random (- 32 lsb))))

(define (regmask->reglist mask)
  (format "{~a}"
          (string-join
           (for/list ([i (in-range 8)]
                      #:when (= (bitwise-bit-field mask i (add1 i)) 1))
             (format "r~a" i))
           ", ")))

(define (same asm kind) (sample asm asm kind))

(define generators
  (list
   (lambda ()
     (define mnemonic (op (pick '("and" "eor" "sub" "rsb" "add" "adc" "sbc" "rsc" "orr" "bic"
                                  "ands" "eors" "subs" "rsbs" "adds" "adcs" "sbcs" "rscs"
                                  "orrs" "bics"))))
     (same (asm-line mnemonic (list (r) (r) (r))) 'dp-reg))
   (lambda ()
     (define mnemonic (op (pick '("and" "eor" "sub" "rsb" "add" "adc" "sbc" "rsc" "orr" "bic"
                                  "ands" "eors" "subs" "rsbs" "adds" "adcs" "sbcs" "rscs"
                                  "orrs" "bics"))))
     (same (asm-line mnemonic (list (r) (r) (imm imm8s))) 'dp-imm))
   (lambda ()
     (define mnemonic (op (pick '("and" "eor" "sub" "rsb" "add" "adc" "sbc" "rsc" "orr" "bic"
                                  "ands" "eors" "subs" "rsbs" "adds" "adcs" "sbcs" "rscs"
                                  "orrs" "bics"))))
     (define shf (pick shift-ops))
     (define amount (shift-imm shf))
     (same (asm-line mnemonic (list (r) (r) (r) (format "~a ~a" shf amount))) 'dp-shift-imm))
   (lambda ()
     (define mnemonic (op (pick '("mov" "mvn" "movs" "mvns"))))
     (same (asm-line mnemonic (list (r) (r))) 'mov-reg))
   (lambda ()
     (define mnemonic (op (pick '("mov" "mvn" "movs" "mvns"))))
     (same (asm-line mnemonic (list (r) (imm imm8s))) 'mov-imm))
   (lambda ()
     (define mnemonic (op (pick '("mov" "mvn" "movs" "mvns"))))
     (define shf (pick shift-ops))
     (define amount (shift-imm shf))
     (same (asm-line mnemonic (list (r) (r) (format "~a ~a" shf amount))) 'mov-shift-imm))
   (lambda ()
     (define mnemonic (op (pick '("tst" "teq" "cmp" "cmn"))))
     (same (asm-line mnemonic (list (r) (r))) 'test-reg))
   (lambda ()
     (define mnemonic (op (pick '("tst" "teq" "cmp" "cmn"))))
     (same (asm-line mnemonic (list (r) (imm imm8s))) 'test-imm))
   (lambda ()
     (define mnemonic (op (pick shift-ops)))
     (define amount (shift-imm (regexp-replace #rx"(eq|ne|cs|cc|mi|pl|vs|vc|hi|ls|ge|lt|gt|le)$"
                                               mnemonic
                                               "")))
     (same (asm-line mnemonic (list (r) (r) amount)) 'shift-imm))
   (lambda ()
     (define mnemonic (op (pick shift-ops)))
     (same (asm-line mnemonic (list (r) (r) (r))) 'shift-reg))
   (lambda ()
     (define mnemonic (op (pick '("movw" "movt"))))
     (same (asm-line mnemonic (list (r) (imm imm16s))) 'movw-movt))
   (lambda ()
     (define mnemonic (op (pick '("mul" "muls" "smmul" "sdiv" "udiv"))))
     (same (asm-line mnemonic (list (r) (r) (r))) 'mul-div))
   (lambda ()
     (define mnemonic (op (pick '("mla" "mlas" "mls" "smmla" "smmls"))))
     (same (asm-line mnemonic (list (r) (r) (r) (r))) 'mul-acc))
   (lambda ()
     (define mnemonic (op (pick '("smull" "umull" "smulls" "umulls"
                                  "smlal" "umlal" "smlals" "umlals"))))
     (match-define (list rdlo rdhi) (distinct-regs 2))
     (same (asm-line mnemonic (list rdlo rdhi (r) (r))) 'long-mul))
   (lambda ()
     (define mnemonic (op (pick '("uxtah" "uxth" "uxtb" "rev" "rev16" "revsh" "rbit" "clz"))))
     (if (regexp-match? #rx"uxtah" mnemonic)
         (same (asm-line mnemonic (list (r) (r) (r))) 'extend)
         (same (asm-line mnemonic (list (r) (r))) 'extend-reverse)))
   (lambda ()
     (define lsb (random 24))
     (define width (min (bitfield-width lsb) 8))
     (define mnemonic (op (pick '("bfi" "sbfx" "ubfx"))))
     (same (asm-line mnemonic (list (r) (r) (format "#~a" lsb) (format "#~a" width))) 'bitfield))
   (lambda ()
     (define lsb (random 24))
     (define width (min (bitfield-width lsb) 8))
     (define mnemonic (op "bfc"))
     (same (asm-line mnemonic (list (r) (format "#~a" lsb) (format "#~a" width))) 'bitfield-clear))
   (lambda ()
     (define mnemonic (op (pick '("ldr" "str"))))
     (define offset (* 4 (random 16)))
     (same (asm-line mnemonic (list (r) (format "[~a, ~a]" (r) (signed-imm offset)))) 'word-transfer-imm))
   (lambda ()
     (define mnemonic (op (pick '("ldr" "str" "ldrb" "strb"))))
     (same (asm-line mnemonic (list (r) (format "[~a, ~a]" (r) (r)))) 'word-transfer-reg))
   (lambda ()
     (define mnemonic (op (pick '("ldrb" "strb" "ldrh" "strh" "ldrsb" "ldrsh"))))
     (define offset (random 256))
     (same (asm-line mnemonic (list (r) (format "[~a, ~a]" (r) (signed-imm offset)))) 'small-transfer-imm))
   (lambda ()
     (define mnemonic (op (pick '("ldrh" "strh" "ldrsb" "ldrsh"))))
     (same (asm-line mnemonic (list (r) (format "[~a, ~a]" (r) (r)))) 'halfword-transfer-reg))
   (lambda ()
     (define mnemonic (op (pick '("swp" "swpb"))))
     (match-define (list rd rm rn) (distinct-regs 3))
     (same (asm-line mnemonic (list rd rm (format "[~a]" rn))) 'swap))
   (lambda ()
     (define mnemonic (op (pick '("ldm" "stm"))))
     (define mask (pick '(1 2 3 4 5 6 7 8 9 10 15 31 63 127 255)))
     (define rn (r))
     (sample (asm-line mnemonic (list rn (format "#~a" mask)))
             (asm-line mnemonic (list rn (regmask->reglist mask)))
             'block-transfer))))

(define (greenthumb-word gt-asm)
  (define code (send printer encode (send parser ir-from-string gt-asm)))
  (arm-inst->word machine (vector-ref code 0)))

(define (run-tool exe args)
  (define out (open-output-string))
  (define err (open-output-string))
  (define ok?
    (parameterize ([current-output-port out]
                   [current-error-port err])
      (apply system* exe args)))
  (values ok? (get-output-string out) (get-output-string err)))

(define (bytes->word-le bs)
  (unless (= (bytes-length bs) 4)
    (raise-user-error 'test-random-encodings
                      "expected exactly 4 text bytes, got ~a" (bytes-length bs)))
  (for/sum ([b (in-bytes bs)] [shift (in-list '(0 8 16 24))])
    (arithmetic-shift b shift)))

(define (assemble-word as-asm)
  (define tmpdir (make-temporary-file "gt-arm-encoding-~a" 'directory "/tmp"))
  (define asm-file (build-path tmpdir "one.s"))
  (define obj-file (build-path tmpdir "one.o"))
  (define bin-file (build-path tmpdir "one.bin"))
  (dynamic-wind
    void
    (lambda ()
      (call-with-output-file asm-file #:exists 'truncate
        (lambda (out)
          (fprintf out ".syntax unified\n")
          (fprintf out ".arm\n")
          (fprintf out ".arch ~a\n" arch)
          (fprintf out ".text\n")
          (fprintf out ".global _start\n")
          (fprintf out "_start:\n")
          (display as-asm out)))
      (define-values (as-ok? as-out as-err)
        (run-tool as-path (list (format "-march=~a" arch)
                                "-o" (path->string obj-file)
                                (path->string asm-file))))
      (unless as-ok?
        (raise-user-error 'test-random-encodings
                          "assembler failed for:\n~a\nstdout:\n~astderr:\n~a"
                          as-asm as-out as-err))
      (define-values (obj-ok? obj-out obj-err)
        (run-tool objcopy-path (list "-O" "binary" "-j" ".text"
                                     (path->string obj-file)
                                     (path->string bin-file))))
      (unless obj-ok?
        (raise-user-error 'test-random-encodings
                          "objcopy failed for:\n~a\nstdout:\n~astderr:\n~a"
                          as-asm obj-out obj-err))
      (bytes->word-le (file->bytes bin-file)))
    (lambda () (delete-directory/files tmpdir #:must-exist? #f))))

(define (hex32 n)
  (string-append "0x" (~r (bitwise-and n #xffffffff)
                         #:base 16
                         #:min-width 8
                         #:pad-string "0")))

(define started-at (current-inexact-milliseconds))

(define (maybe-print-progress done)
  (when (and (> progress-interval 0)
             (or (= done count) (= (remainder done progress-interval) 0)))
    (define elapsed-seconds (/ (- (current-inexact-milliseconds) started-at) 1000.0))
    (define rate (if (> elapsed-seconds 0) (/ done elapsed-seconds) 0))
    (printf "progress: ~a/~a checked (~a%), ~a/s\n"
            done
            count
            (~r (* 100.0 (/ done count)) #:precision '(= 1))
            (~r rate #:precision '(= 1)))
    (flush-output)))

(printf "checking ~a random ARM encodings against ~a using ~a (~a)\n"
        count as-path objcopy-path arch)
(flush-output)

(for ([i (in-range count)])
  (define s ((pick generators)))
  (define gt-word (greenthumb-word (sample-gt-asm s)))
  (define as-word (assemble-word (sample-as-asm s)))
  (when verbose?
    (printf "~a ~a ~a => ~a\n" i (sample-kind s) (string-trim (sample-gt-asm s)) (hex32 gt-word)))
  (unless (= gt-word as-word)
    (raise-user-error 'test-random-encodings
                      "encoding mismatch at sample ~a (~a)\n  greenthumb asm: ~a\n  assembler asm:  ~a\n  greenthumb:     ~a\n  assembler:      ~a"
                      i
                      (sample-kind s)
                      (string-trim (sample-gt-asm s))
                      (string-trim (sample-as-asm s))
                      (hex32 gt-word)
                      (hex32 as-word)))
  (maybe-print-progress (add1 i)))

(printf "checked ~a random ARM encodings against ~a using ~a (~a)\n"
        count as-path objcopy-path arch)
