#lang racket

(require rackunit
         racket/string
         "../../memory-racket.rkt"
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-simulator-racket.rkt")

(define parser (new arm-parser%))
(define machine (new arm-machine% [config 16]))
(define printer (new arm-printer% [machine machine]))
(define simulator (new arm-simulator-racket% [machine machine]))

(define interesting-values
  '(0 1 #xffffffff #x80000000 #x7fffffff #x12345678 #xffff0001))

(define signed-interesting-values
  '(0 1 -1 -2 -2147483648 2147483647 #x12345678))

(define accumulator-values '(0 1 #xffffffff #x80000000))
(define flag-check-values '(0 1 #xffffffff #x80000000))
(define shift-amounts '(0 1 31 32 33 255))
(define flag-values (build-list 16 values))
(define live-flag-masks '(0 #b1111 #b1100 #b0010 #b0011))
(define shift-mnemonics '("lsl" "lsr" "asr" "ror"))
(define word-mask #xffffffff)

(define (u32 value)
  (bitwise-and value word-mask))

(define (s32 value)
  (define masked (u32 value))
  (if (>= masked #x80000000)
      (- masked #x100000000)
      masked))

(define (parse-code source)
  (send parser ir-from-string source))

(define (encode source)
  (send printer encode (parse-code source)))

(define (state-with regs [memory #f] [flags 0])
  (progstate (vector-copy regs)
             (if memory (send memory clone) (new memory-racket%))
             flags))

(define (run source regs [memory #f] [flags 0])
  (send simulator interpret (encode source) (state-with regs memory flags)))

(define (reg state id)
  (vector-ref (progstate-regs state) id))

(define (base-regs)
  (define regs (make-vector 16 0))
  (vector-set! regs 15 #x1000)
  regs)

(define (join-lines . lines)
  (string-append (string-join lines "\n") "\n"))

(define (lines->source lines)
  (if (null? lines) "" (apply join-lines lines)))

(define (store-word-bytes! memory address value)
  (for ([i (in-range 4)])
    (send memory store (+ address i)
          (bitwise-and (arithmetic-shift value (* -8 i)) #xff))))

(define (memory-byte state address)
  (or (send (progstate-memory state) lookup-update address) 0))

(define (memory-word state address)
  (for/fold ([word 0]) ([i (in-range 4)])
    (bitwise-ior word (arithmetic-shift (memory-byte state (+ address i)) (* 8 i)))))

(define (mul-unrolled32 rd rm rs t0 t1 t2)
  (string-append
   (join-lines
    (format "mov ~a, ~a" t0 rm)
    (format "mov ~a, ~a" t1 rs)
    (format "mov ~a, #0" rd))
   (apply string-append
          (for/list ([_ (in-range 32)])
            (join-lines
             (format "and ~a, ~a, #1" t2 t1)
             (format "rsb ~a, ~a, #0" t2 t2)
             (format "and ~a, ~a, ~a" t2 t0 t2)
             (format "add ~a, ~a, ~a" rd rd t2)
             (format "mov ~a, ~a, lsr #1" t1 t1)
             (format "mov ~a, ~a, lsl #1" t0 t0))))))

(define (umull-via-mul16 rdlo rdhi rm rs t0 t1 t2 t3 t4 t5 t6 t7 t8)
  (join-lines
   (format "mov ~a, ~a, lsl #16" t0 rm)
   (format "mov ~a, ~a, lsr #16" t0 t0)
   (format "mov ~a, ~a, lsr #16" t1 rm)
   (format "mov ~a, ~a, lsl #16" t2 rs)
   (format "mov ~a, ~a, lsr #16" t2 t2)
   (format "mov ~a, ~a, lsr #16" t3 rs)
   (format "mul ~a, ~a, ~a" t4 t0 t2)
   (format "mul ~a, ~a, ~a" t5 t0 t3)
   (format "mul ~a, ~a, ~a" t6 t1 t2)
   (format "mul ~a, ~a, ~a" t7 t1 t3)
   (format "adds ~a, ~a, ~a" t8 t5 t6)
   (format "mov ~a, #0" t6)
   (format "adc ~a, ~a, #0" t6 t6)
   (format "mov ~a, ~a, lsl #16" t6 t6)
   (format "mov ~a, ~a, lsl #16" rdlo t8)
   (format "adds ~a, ~a, ~a" rdlo t4 rdlo)
   (format "adc ~a, ~a, ~a, lsr #16" rdhi t7 t8)
   (format "add ~a, ~a, ~a" rdhi rdhi t6)))

(define (umull-via-mul16-preserve rdlo rdhi rm rs t0 t1 t2 t3 t4 t5 t6 t7 t8 t9)
  (join-lines
   (format "mov ~a, ~a, lsl #16" t0 rm)
   (format "mov ~a, ~a, lsr #16" t0 t0)
   (format "mov ~a, ~a, lsr #16" t1 rm)
   (format "mov ~a, ~a, lsl #16" t2 rs)
   (format "mov ~a, ~a, lsr #16" t2 t2)
   (format "mov ~a, ~a, lsr #16" t3 rs)
   (format "mul ~a, ~a, ~a" t4 t0 t2)
   (format "mul ~a, ~a, ~a" t5 t0 t3)
   (format "mul ~a, ~a, ~a" t6 t1 t2)
   (format "mul ~a, ~a, ~a" t7 t1 t3)
   (format "add ~a, ~a, ~a" t8 t5 t6)
   (format "and ~a, ~a, ~a" t9 t5 t6)
   (format "orr ~a, ~a, ~a" t5 t5 t6)
   (format "mvn ~a, ~a" t6 t8)
   (format "and ~a, ~a, ~a" t5 t5 t6)
   (format "orr ~a, ~a, ~a" t9 t9 t5)
   (format "mov ~a, ~a, lsr #31" t9 t9)
   (format "mov ~a, ~a, lsl #16" t9 t9)
   (format "mov ~a, ~a, lsl #16" t5 t8)
   (format "add ~a, ~a, ~a" rdlo t4 t5)
   (format "and ~a, ~a, ~a" t6 t4 t5)
   (format "orr ~a, ~a, ~a" t5 t4 t5)
   (format "mvn ~a, ~a" t4 rdlo)
   (format "and ~a, ~a, ~a" t5 t5 t4)
   (format "orr ~a, ~a, ~a" t6 t6 t5)
   (format "mov ~a, ~a, lsr #31" t6 t6)
   (format "mov ~a, ~a, lsr #16" rdhi t8)
   (format "add ~a, ~a, ~a" rdhi t7 rdhi)
   (format "add ~a, ~a, ~a" rdhi rdhi t9)
   (format "add ~a, ~a, ~a" rdhi rdhi t6)))

(define (mul32-nz-suffix rd)
  (format "tst ~a, ~a\n" rd rd))

(define (mull64-nz-suffix rdlo rdhi t0 t1)
  (join-lines
   (format "mov ~a, ~a, lsl #1" t0 rdhi)
   (format "mov ~a, ~a, lsr #1" t0 t0)
   (format "orr ~a, ~a, ~a, lsr #1" t0 t0 rdlo)
   (format "and ~a, ~a, #1" t1 rdlo)
   (format "orr ~a, ~a, ~a" t0 t0 t1)
   (format "mov ~a, ~a, lsr #31" t1 rdhi)
   (format "mov ~a, ~a, lsl #31" t1 t1)
   (format "orr ~a, ~a, ~a" t0 t0 t1)
   (format "tst ~a, ~a" t0 t0)))

(define (smull-via-recursive-umull rdlo rdhi rm rs temps)
  (string-append
   (apply umull-via-mul16 rdlo rdhi rm rs temps)
   (join-lines
    (format "tst ~a, ~a" rm rm)
    (format "submi ~a, ~a, ~a" rdhi rdhi rs)
    (format "tst ~a, ~a" rs rs)
    (format "submi ~a, ~a, ~a" rdhi rdhi rm))))

(define (smull-via-recursive-umull-preserve rdlo rdhi rm rs temps t0 t1)
  (string-append
   (apply umull-via-mul16-preserve rdlo rdhi rm rs temps)
   (join-lines
    (format "mov ~a, ~a, asr #31" t0 rm)
    (format "and ~a, ~a, ~a" t0 t0 rs)
    (format "sub ~a, ~a, ~a" rdhi rdhi t0)
    (format "mov ~a, ~a, asr #31" t1 rs)
    (format "and ~a, ~a, ~a" t1 t1 rm)
    (format "sub ~a, ~a, ~a" rdhi rdhi t1))))

(define (umlal-via-recursive-umull)
  (string-append
   (umull-via-mul16 "r4" "r5" "r2" "r3"
                    "r6" "r7" "r8" "r9" "r10" "r11" "r12" "r13" "r14")
   (join-lines
    "adds r0, r0, r4"
    "adc r1, r1, r5")))

(define (umlal-via-umull-preserve)
  (string-append
   (join-lines
    "mov r4, r0"
    "mov r5, r1"
    "umull r0, r1, r2, r3"
    "mov r6, r0"
    "add r0, r0, r4"
    "and r7, r6, r4"
    "orr r6, r6, r4"
    "mvn r4, r0"
    "and r6, r6, r4"
    "orr r7, r7, r6"
    "mov r7, r7, lsr #31"
    "add r1, r1, r5"
    "add r1, r1, r7")))

(define (smlal-via-recursive-smull)
  (string-append
   (smull-via-recursive-umull "r4" "r5" "r2" "r3"
                              '("r6" "r7" "r8" "r9" "r10" "r11" "r12" "r13" "r14"))
   (join-lines
    "adds r0, r0, r4"
    "adc r1, r1, r5")))

(define (smlal-via-smull-preserve)
  (string-append
   (join-lines
    "mov r4, r0"
    "mov r5, r1"
    "smull r0, r1, r2, r3"
    "mov r6, r0"
    "add r0, r0, r4"
    "and r7, r6, r4"
    "orr r6, r6, r4"
    "mvn r4, r0"
    "and r6, r6, r4"
    "orr r7, r7, r6"
    "mov r7, r7, lsr #31"
    "add r1, r1, r5"
    "add r1, r1, r7")))

(define (logical-s-rsr-line op rd rn operand)
  (cond
   [(member op '("movs" "mvns")) (format "~a ~a, ~a" op rd operand)]
   [(member op '("tst" "teq")) (format "~a ~a, ~a" op rn operand)]
   [else (format "~a ~a, ~a, ~a" op rd rn operand)]))

(define (logical-s-rsr-source op shift)
  (cond
   [(member op '("movs" "mvns"))
    (format "~a r0, r2, ~a r3\n" op shift)]
   [(member op '("tst" "teq"))
    (format "~a r1, r2, ~a r3\n" op shift)]
   [else
    (format "~a r0, r1, r2, ~a r3\n" op shift)]))

(define (logical-s-rsr-linear-exact op shift amount)
  (define masked (bitwise-and amount #xff))
  (define shift-lines
    (cond
     [(= masked 0) (join-lines "mov r4, r2")]
     [else
      (string-append
       (join-lines "mov r4, r2")
       (apply string-append
              (for/list ([_ (in-range (sub1 masked))])
                (join-lines (format "mov r4, r4, ~a #1" shift))))
       (join-lines (format "movs r4, r4, ~a #1" shift)))]))
  (string-append
   shift-lines
   (join-lines (logical-s-rsr-line op "r0" "r1" "r4"))))

(define (barrel-stage-source shift masked)
  (lines->source
   (for/list ([step '(1 2 4 8 16)]
              #:when (not (zero? (bitwise-and masked step))))
     (format "movs r4, r4, ~a #~a" shift step))))

(define (logical-s-rsr-barrel-exact op shift amount)
  (define masked (bitwise-and amount #xff))
  (define body
    (cond
     [(zero? masked) ""]
     [(and (member shift '("lsl" "lsr"))
           (not (zero? (bitwise-and masked #xe0))))
      (if (= masked 32)
          (join-lines
           "mov r4, #0"
           "mov r6, r2"
           (format "movs r6, r6, ~a #1"
                   (if (equal? shift "lsl") "lsr" "lsl")))
          (join-lines
           "mov r4, #0"
           "mov r6, #0"
           (format "movs r6, r6, ~a #1"
                   (if (equal? shift "lsl") "lsr" "lsl"))))]
     [(and (equal? shift "asr")
           (not (zero? (bitwise-and masked #xe0))))
      (join-lines
       "mov r4, r2, asr #31"
       "movs r6, r2, lsl #1")]
     [(and (equal? shift "ror")
           (zero? (bitwise-and masked #x1f)))
      (join-lines
       "movs r6, r4, lsl #1")]
     [else (barrel-stage-source shift masked)]))
  (string-append
   (join-lines
    "mov r4, r2"
    "and r5, r3, #255")
   body
   (join-lines (logical-s-rsr-line op "r0" "r1" "r4"))))

(define (non-s-rsr-source op shift)
  (cond
   [(member op '("mov" "mvn"))
    (format "~a r0, r2, ~a r3\n" op shift)]
   [else
    (format "~a r0, r1, r2, ~a r3\n" op shift)]))

(define (non-s-rsr-line op)
  (cond
   [(member op '("mov" "mvn")) (format "~a r0, r4" op)]
   [else (format "~a r0, r1, r4" op)]))

(define (variable-shift-xor-step-source shift log2 amount)
  (join-lines
   (if (= log2 0)
       "mov r6, r5"
       (format "mov r6, r5, lsr #~a" log2))
   "and r6, r6, #1"
   "rsb r6, r6, #0"
   (format "mov r7, r4, ~a #~a" shift amount)
   "eor r7, r4, r7"
   "and r7, r7, r6"
   "eor r4, r4, r7"))

(define (variable-shift-preserve-overflow-source shift)
  (cond
   [(member shift '("lsl" "lsr"))
    (join-lines
     "mov r6, r5, lsr #5"
     "rsb r7, r6, #0"
     "orr r6, r6, r7"
     "mov r6, r6, lsr #31"
     "rsb r6, r6, #0"
     "mvn r7, r6"
     "and r4, r4, r7")]
   [(equal? shift "asr")
    (join-lines
     "mov r6, r5, lsr #5"
     "rsb r7, r6, #0"
     "orr r6, r6, r7"
     "mov r6, r6, lsr #31"
     "rsb r6, r6, #0"
     "mov r7, r2, asr #31"
     "and r7, r7, r6"
     "mvn r6, r6"
     "and r4, r4, r6"
     "orr r4, r4, r7")]
   [else ""]))

(define (variable-shift-xor-preserve shift result-line)
  (string-append
   (join-lines
    "mov r4, r2"
    "and r5, r3, #255")
   (apply string-append
          (for/list ([log2 '(0 1 2 3 4)]
                     [amount '(1 2 4 8 16)])
            (variable-shift-xor-step-source shift log2 amount)))
   (variable-shift-preserve-overflow-source shift)
   (join-lines result-line)))

(define (block-start-offset count pre-index? up?)
  (define byte-count (* count 4))
  (cond
   [(and up? pre-index?) 4]
   [up? 0]
   [pre-index? (- byte-count)]
   [else (+ (- byte-count) 4)]))

(define (block-mode-name load? pre-index? up?)
  (define stem (if load? "ldm" "stm"))
  (cond
   [(and pre-index? up?) (string-append stem "ib")]
   [(and pre-index? (not up?)) (string-append stem "db")]
   [(and (not pre-index?) up?) (string-append stem "ia")]
   [else (string-append stem "da")]))

(define (block-source load? pre-index? up? writeback?)
  (format "~a r13~a, {r0, r1, r2}\n"
          (block-mode-name load? pre-index? up?)
          (if writeback? "!" "")))

(define (block-replacement-source load? pre-index? up? writeback?)
  (define start (block-start-offset 3 pre-index? up?))
  (define xfer (if load? "ldr" "str"))
  (define steps
    (for/list ([reg '(0 1 2)]
               [idx (in-naturals)])
      (format "~a r~a, [r13, #~a]" xfer reg (+ start (* idx 4)))))
  (apply join-lines
         (if writeback?
             (append steps
                     (list (format "~a r13, r13, #12"
                                   (if up? "add" "sub"))))
             steps)))

(define (check-regs-match original-source replacement-source regs live-regs)
  (check-live-match original-source replacement-source regs live-regs))

(define (check-live-match original-source replacement-source regs live-regs
                          #:flags [flags 0]
                          #:live-flags [live-flags 0]
                          #:memory [memory #f]
                          #:memory-addresses [memory-addresses '()])
  (define original (run original-source regs memory flags))
  (define replacement (run replacement-source regs memory flags))
  (for ([id live-regs])
    (check-equal? (u32 (reg replacement id)) (u32 (reg original id))
                  (format "r~a differs for\n~a\nvs\n~a"
                          id original-source replacement-source)))
  (when (not (= live-flags 0))
    (check-equal? (bitwise-and (progstate-z replacement) live-flags)
                  (bitwise-and (progstate-z original) live-flags)
                  (format "live flags mask ~a differs for flags ~a\n~a\nvs\n~a"
                          live-flags flags original-source replacement-source)))
  (for ([address memory-addresses])
    (check-equal? (memory-word replacement address) (memory-word original address)
                  (format "memory word @~a differs for\n~a\nvs\n~a"
                          address original-source replacement-source))))

(test-case "oracle: MUL unrolled32 matches low 32-bit multiply"
  (for* ([rm interesting-values]
         [rs interesting-values])
    (define regs (base-regs))
    (vector-set! regs 1 rm)
    (vector-set! regs 2 rs)
    (check-regs-match "mul r0, r1, r2\n"
                      (mul-unrolled32 "r0" "r1" "r2" "r4" "r5" "r6")
                      regs
                      '(0))))

(test-case "oracle: MLA via MUL+ADD matches live result"
  (for* ([rm interesting-values]
         [rs interesting-values]
         [rn interesting-values])
    (define regs (base-regs))
    (vector-set! regs 1 rm)
    (vector-set! regs 2 rs)
    (vector-set! regs 3 rn)
    (check-regs-match "mla r0, r1, r2, r3\n"
                      "mul r4, r1, r2\nadd r0, r4, r3\n"
                      regs
                      '(0))))

(test-case "oracle: UMULL via 16x16 MULs matches 64-bit product"
  (for* ([rm interesting-values]
         [rs interesting-values])
    (define regs (base-regs))
    (vector-set! regs 2 rm)
    (vector-set! regs 3 rs)
    (check-regs-match "umull r0, r1, r2, r3\n"
                      (umull-via-mul16 "r0" "r1" "r2" "r3"
                                       "r4" "r5" "r6" "r7" "r8" "r9" "r10" "r11" "r12")
                      regs
                      '(0 1))))

(test-case "oracle: recursive SMULL via UMULL-via-MULs matches signed 64-bit product"
  (for* ([rm signed-interesting-values]
         [rs signed-interesting-values])
    (define regs (base-regs))
    (vector-set! regs 2 rm)
    (vector-set! regs 3 rs)
    (check-regs-match "smull r0, r1, r2, r3\n"
                      (smull-via-recursive-umull "r0" "r1" "r2" "r3"
                                                 '("r4" "r5" "r6" "r7" "r8" "r9" "r10" "r11" "r12"))
                      regs
                      '(0 1))))

(test-case "oracle: UMLAL via recursive UMULL plus 64-bit add matches accumulator"
  (for* ([rm interesting-values]
         [rs interesting-values]
         [rdlo accumulator-values]
         [rdhi accumulator-values])
    (define regs (base-regs))
    (vector-set! regs 0 rdlo)
    (vector-set! regs 1 rdhi)
    (vector-set! regs 2 rm)
    (vector-set! regs 3 rs)
    (check-regs-match "umlal r0, r1, r2, r3\n"
                      (umlal-via-recursive-umull)
                      regs
                      '(0 1))))

(test-case "oracle: SMLAL via recursive SMULL plus 64-bit add matches accumulator"
  (for* ([rm signed-interesting-values]
         [rs signed-interesting-values]
         [rdlo accumulator-values]
         [rdhi accumulator-values])
    (define regs (base-regs))
    (vector-set! regs 0 rdlo)
    (vector-set! regs 1 rdhi)
    (vector-set! regs 2 rm)
    (vector-set! regs 3 rs)
    (check-regs-match "smlal r0, r1, r2, r3\n"
                      (smlal-via-recursive-smull)
                      regs
                      '(0 1))))

(test-case "oracle: MUL and MLA preserve or set live flag masks"
  (for* ([rm flag-check-values]
         [rs flag-check-values]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 1 rm)
    (vector-set! regs 2 rs)
    (check-live-match "mul r0, r1, r2\n"
                      (mul-unrolled32 "r0" "r1" "r2" "r4" "r5" "r6")
                      regs
                      '(0)
                      #:flags flags
                      #:live-flags live-flags)
    (check-live-match "muls r0, r1, r2\n"
                      (string-append
                       (mul-unrolled32 "r0" "r1" "r2" "r4" "r5" "r6")
                       (mul32-nz-suffix "r0"))
                      regs
                      '(0)
                      #:flags flags
                      #:live-flags live-flags))
  (for* ([rm flag-check-values]
         [rs flag-check-values]
         [rn flag-check-values]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 1 rm)
    (vector-set! regs 2 rs)
    (vector-set! regs 3 rn)
    (check-live-match "mla r0, r1, r2, r3\n"
                      "mul r4, r1, r2\nadd r0, r4, r3\n"
                      regs
                      '(0)
                      #:flags flags
                      #:live-flags live-flags)
    (check-live-match "mlas r0, r1, r2, r3\n"
                      "mul r4, r1, r2\nadd r0, r4, r3\ntst r0, r0\n"
                      regs
                      '(0)
                      #:flags flags
                      #:live-flags live-flags)))

(test-case "oracle: long multiply variants preserve or set live flag masks"
  (for* ([rm flag-check-values]
         [rs flag-check-values]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 2 rm)
    (vector-set! regs 3 rs)
    (define umull-preserve
      (umull-via-mul16-preserve "r0" "r1" "r2" "r3"
                                "r4" "r5" "r6" "r7" "r8" "r9" "r10" "r11" "r12" "r13"))
    (check-live-match "umull r0, r1, r2, r3\n"
                      umull-preserve
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags)
    (check-live-match "umulls r0, r1, r2, r3\n"
                      (string-append umull-preserve
                                     (mull64-nz-suffix "r0" "r1" "r4" "r5"))
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags))
  (for* ([rm '(0 1 -1 #x80000000)]
         [rs '(0 1 -1 #x7fffffff)]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 (s32 rs))
    (define smull-preserve
      (smull-via-recursive-umull-preserve
       "r0" "r1" "r2" "r3"
       '("r4" "r5" "r6" "r7" "r8" "r9" "r10" "r11" "r12" "r13")
       "r4"
       "r5"))
    (check-live-match "smull r0, r1, r2, r3\n"
                      smull-preserve
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags)
    (check-live-match "smulls r0, r1, r2, r3\n"
                      (string-append smull-preserve
                                     (mull64-nz-suffix "r0" "r1" "r4" "r5"))
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags)))

(test-case "oracle: long multiply accumulate writeback and flag suffix variants"
  (for* ([rm flag-check-values]
         [rs flag-check-values]
         [rdlo accumulator-values]
         [rdhi accumulator-values]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 0 rdlo)
    (vector-set! regs 1 rdhi)
    (vector-set! regs 2 rm)
    (vector-set! regs 3 rs)
    (define umlal-preserve (umlal-via-umull-preserve))
    (check-live-match "umlal r0, r1, r2, r3\n"
                      umlal-preserve
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags)
    (check-live-match "umlals r0, r1, r2, r3\n"
                      (string-append umlal-preserve
                                     (mull64-nz-suffix "r0" "r1" "r4" "r5"))
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags))
  (for* ([rm '(0 1 -1 #x80000000)]
         [rs '(0 1 -1 #x7fffffff)]
         [rdlo accumulator-values]
         [rdhi accumulator-values]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 0 rdlo)
    (vector-set! regs 1 rdhi)
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 (s32 rs))
    (define smlal-preserve (smlal-via-smull-preserve))
    (check-live-match "smlal r0, r1, r2, r3\n"
                      smlal-preserve
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags)
    (check-live-match "smlals r0, r1, r2, r3\n"
                      (string-append smlal-preserve
                                     (mull64-nz-suffix "r0" "r1" "r4" "r5"))
                      regs
                      '(0 1)
                      #:flags flags
                      #:live-flags live-flags)))

(test-case "oracle: register-shifted-register MOV LSL via standalone shift"
  (for* ([rm interesting-values]
         [rs shift-amounts])
    (define regs (base-regs))
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 rs)
    (check-regs-match "mov r0, r2, lsl r3\n"
                      "lsl r4, r2, r3\nmov r0, r4\n"
                      regs
                      '(0))))

(test-case "oracle: ADD with materialized RSR operand matches ADD LSL register"
  (for* ([rm interesting-values]
         [rn interesting-values]
         [rs shift-amounts])
    (define regs (base-regs))
    (vector-set! regs 1 (s32 rn))
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 rs)
    (check-regs-match "add r0, r1, r2, lsl r3\n"
                      "lsl r4, r2, r3\nadd r0, r1, r4\n"
                      regs
                      '(0))))

(test-case "oracle: non-S RSR lowering preserves live flag masks across shift kinds"
  (for* ([shift shift-mnemonics]
         [rm flag-check-values]
         [rn flag-check-values]
         [rs shift-amounts]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 1 (s32 rn))
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 rs)
    (check-live-match (format "mov r0, r2, ~a r3\n" shift)
                      (format "~a r4, r2, r3\nmov r0, r4\n" shift)
                      regs
                      '(0)
                      #:flags flags
                      #:live-flags live-flags)
    (check-live-match (format "add r0, r1, r2, ~a r3\n" shift)
                      (format "~a r4, r2, r3\nadd r0, r1, r4\n" shift)
                      regs
                      '(0)
                      #:flags flags
                      #:live-flags live-flags)))

(test-case "oracle: non-S RSR preserve template keeps result and live flags"
  (for* ([op '("mov" "mvn" "and" "bic" "add" "adc")]
         [shift shift-mnemonics]
         [rm flag-check-values]
         [rn flag-check-values]
         [rs shift-amounts]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 1 (s32 rn))
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 rs)
    (check-live-match (non-s-rsr-source op shift)
                      (variable-shift-xor-preserve
                       shift
                       (non-s-rsr-line op))
                      regs
                      '(0)
                      #:flags flags
                      #:live-flags live-flags)))

(test-case "oracle: logical/test/move S RSR exact-carry loop sets live flags"
  (for* ([op '("ands" "eors" "orrs" "bics" "movs" "mvns" "tst" "teq")]
         [shift shift-mnemonics]
         [rm flag-check-values]
         [rn flag-check-values]
         [rs shift-amounts]
         [flags '(0 #b0010 #b0101 #b1111)]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 1 (s32 rn))
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 rs)
    (check-live-match
     (cond
      [(member op '("movs" "mvns"))
       (format "~a r0, r2, ~a r3\n" op shift)]
      [(member op '("tst" "teq"))
       (format "~a r1, r2, ~a r3\n" op shift)]
      [else
       (format "~a r0, r1, r2, ~a r3\n" op shift)])
     (logical-s-rsr-linear-exact op shift rs)
     regs
     (if (member op '("tst" "teq")) '() '(0))
     #:flags flags
     #:live-flags live-flags)))

(test-case "oracle: logical/test/move S RSR exact-carry barrel sets live flags"
  (for* ([op '("ands" "eors" "orrs" "bics" "movs" "mvns" "tst" "teq")]
         [shift shift-mnemonics]
         [rm flag-check-values]
         [rn flag-check-values]
         [rs shift-amounts]
         [flags '(0 #b0010 #b0101 #b1111)]
         [live-flags live-flag-masks])
    (define regs (base-regs))
    (vector-set! regs 1 (s32 rn))
    (vector-set! regs 2 (s32 rm))
    (vector-set! regs 3 rs)
    (check-live-match (logical-s-rsr-source op shift)
                      (logical-s-rsr-barrel-exact op shift rs)
                      regs
                      (if (member op '("tst" "teq")) '() '(0))
                      #:flags flags
                      #:live-flags live-flags)))

(test-case "oracle: LDM scalar lowering matches POP register order and writeback"
  (define memory (new memory-racket%))
  (store-word-bytes! memory 100 #x11111111)
  (store-word-bytes! memory 104 #x22222222)
  (store-word-bytes! memory 108 #x33333333)
  (define regs (base-regs))
  (vector-set! regs 13 100)
  (define original (run "pop {r0, r1, r2}\n" regs memory))
  (define replacement
    (run (join-lines
          "ldr r0, [r13, #0]"
          "ldr r1, [r13, #4]"
          "ldr r2, [r13, #8]"
          "add r13, r13, #12")
         regs
         memory))
  (for ([id '(0 1 2 13)])
    (check-equal? (reg replacement id) (reg original id))))

(test-case "oracle: STM scalar lowering matches PUSH store order and writeback"
  (define memory (new memory-racket%))
  (define regs (base-regs))
  (vector-set! regs 0 #x11111111)
  (vector-set! regs 1 #x22222222)
  (vector-set! regs 2 #x33333333)
  (vector-set! regs 13 100)
  (define original (run "push {r0, r1, r2}\n" regs memory))
  (define replacement
    (run (join-lines
          "str r0, [r13, #-12]"
          "str r1, [r13, #-8]"
          "str r2, [r13, #-4]"
          "sub r13, r13, #12")
         regs
         memory))
  (for ([addr '(88 92 96)])
    (check-equal? (memory-word replacement addr) (memory-word original addr)))
  (check-equal? (reg replacement 13) (reg original 13)))

(test-case "oracle: LDM/STM scalar lowering covers addressing modes and writeback"
  (for* ([load? '(#t #f)]
         [pre-index? '(#f #t)]
         [up? '(#f #t)]
         [writeback? '(#f #t)]
         [flags flag-values]
         [live-flags live-flag-masks])
    (define memory (new memory-racket%))
    (define regs (base-regs))
    (vector-set! regs 0 #x11111111)
    (vector-set! regs 1 #x22222222)
    (vector-set! regs 2 #x33333333)
    (vector-set! regs 13 100)
    (define start (+ 100 (block-start-offset 3 pre-index? up?)))
    (for ([idx (in-range 3)]
          [value '(#xaaaa0000 #xbbbb1111 #xcccc2222)])
      (store-word-bytes! memory (+ start (* idx 4)) value))
    (check-live-match (block-source load? pre-index? up? writeback?)
                      (block-replacement-source load? pre-index? up? writeback?)
                      regs
                      (cond
                       [load? (if writeback? '(0 1 2 13) '(0 1 2))]
                       [writeback? '(13)]
                       [else '()])
                      #:flags flags
                      #:live-flags live-flags
                      #:memory memory
                      #:memory-addresses
                      (if load?
                          '()
                          (for/list ([idx (in-range 3)])
                            (+ start (* idx 4)))))))
