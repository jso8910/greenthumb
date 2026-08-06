#lang racket

(require racket/format
         racket/match
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-restrictions.rkt"
         "../arm-simulator-racket.rkt"
         "../../inst.rkt")

(define machine (new arm-machine% [config 16]))
(define simulator (new arm-simulator-racket% [machine machine]))
(define parser (new arm-parser%))
(define printer (new arm-printer% [machine machine]))

(define (parse-symbol value)
  (if (equal? value "||") '|| (string->symbol value)))

(define (parse-arg value)
  (define parsed (string->number value))
  (if parsed parsed value))

(define (hex32 word)
  (if word
      (string-append "0x" (~r (bitwise-and word #xffffffff)
                              #:base 16
                              #:min-width 8
                              #:pad-string "0"))
      "#f"))

(define (mk op cond shf args)
  (inst (send machine get-opcode-id (vector op cond shf))
        (list->vector args)))

(define (encode-line op cond shf args)
  (displayln (hex32 (arm-inst->word machine (mk op cond shf args)))))

(define (encoded-inst-result encoded-inst)
  (define word (arm-inst->word machine encoded-inst))
  (if word
      (format "ok ~a" (hex32 word))
      "err encoder returned #f"))

(define (parse-asm-result line)
  (with-handlers ([exn? (lambda (e)
                          (format "err ~a" (string-replace (exn-message e) "\n" "\\n")))])
    (define code (send printer encode (send parser ir-from-string (string-append line "\n"))))
    (cond
      [(not (= (vector-length code) 1))
       (format "err expected one instruction, got ~a" (vector-length code))]
      [else
       (encoded-inst-result (vector-ref code 0))])))

(define (parse-asm-results lines)
  (define fallback-threshold 1)
  (define (fallback)
    (cond
      [(<= (length lines) fallback-threshold)
       (map parse-asm-result lines)]
      [else
       (define mid (quotient (length lines) 2))
       (append (parse-asm-results (take lines mid))
               (parse-asm-results (drop lines mid)))]))
  (cond
    [(null? lines) '()]
    [else
     (with-handlers ([exn? (lambda (_) (fallback))])
       (define code
         (send printer encode
               (send parser ir-from-string
                     (string-append (string-join lines "\n") "\n"))))
       (if (= (vector-length code) (length lines))
           (for/list ([encoded-inst (in-vector code)])
             (with-handlers ([exn? (lambda (e)
                                     (format "err ~a" (string-replace (exn-message e) "\n" "\\n")))])
               (encoded-inst-result encoded-inst)))
           (fallback)))]))

(define (parse-asm-line line)
  (displayln (parse-asm-result line)))

(define (print-encoded-result op cond shf args)
  (with-handlers ([exn? (lambda (e)
                          (format "err ~a" (string-replace (exn-message e) "\n" "\\n")))])
    (define decoded-inst (send printer decode-inst (mk op cond shf args)))
    (define line
      (string-trim
       (with-output-to-string
         (lambda () (send printer print-syntax-inst decoded-inst)))))
    (format "ok ~a" line)))

(define (display-print-encoded-result op cond shf args)
  (with-handlers ([exn? (lambda (e)
                          (displayln
                           (format "err ~a" (string-replace (exn-message e) "\n" "\\n"))))])
    (define decoded-inst (send printer decode-inst (mk op cond shf args)))
    (display "ok ")
    (send printer print-syntax-inst decoded-inst)))

(define (print-encoded-line op cond shf args)
  (display-print-encoded-result op cond shf args))

(define (parse-asm-batch)
  (for ([result (parse-asm-results (sequence->list (in-lines)))])
    (displayln result)))

(define (print-encoded-batch)
  (for ([line (in-lines)])
    (define parts (string-split line "\t" #:trim? #f))
    (match parts
	      [(list op cond shf args ...)
	       (display-print-encoded-result (parse-symbol op)
	                                     (parse-symbol cond)
	                                     (parse-symbol shf)
	                                     (map parse-arg args))]
      [_
       (displayln "err expected tab-separated op cond shf args...")])))

(define (surface-batch)
  (define pending-parse-lines '())
  (define (flush-parse!)
    (when (pair? pending-parse-lines)
      (for ([result (parse-asm-results (reverse pending-parse-lines))])
        (displayln result))
      (set! pending-parse-lines '())))
  (for ([line (in-lines)])
    (define parts (string-split line "\t" #:trim? #f))
    (match parts
      [(list "parse" asm-parts ...)
       (set! pending-parse-lines
             (cons (string-join asm-parts "\t") pending-parse-lines))]
	      [(list "print" op cond shf args ...)
	       (flush-parse!)
	       (display-print-encoded-result (parse-symbol op)
	                                     (parse-symbol cond)
	                                     (parse-symbol shf)
	                                     (map parse-arg args))]
      [_
       (flush-parse!)
       (displayln "err expected tab-separated parse/print request")]))
  (flush-parse!))

(define samples
  (list
   (list "gt_ldr_full_imm_wb_down" "load_ops" "immediate_offset"
         (mk 'ldr-full# '|| '|| '(0 1 12 1 0 1)))
   (list "gt_strb_full_reg_shift" "store_ops" "register_offset"
         (mk 'strb-full '|| 'lsl# '(2 3 4 1 1 0 2)))
   (list "gt_ldrh_full_imm" "hwtfr_load_ops" "immediate_offset"
         (mk 'ldrh-full# '|| '|| '(0 1 2 1 1 0)))
   (list "gt_stm_full_db_wb" "block_store_ops" "base"
         (mk 'stm-full# '|| '|| '(3 5 1 0 1)))
   (list "gt_ldm_full_ia_wb" "block_load_ops" "base"
         (mk 'ldm-full# '|| '|| '(3 5 0 1 1)))))

(define (base-state)
  (send machine get-state
        (lambda (#:min [min #f] #:max [max #f] #:const [const #f])
          (or const 0))))

(define (store-word-bytes! memory address value)
  (for ([i (in-range 4)])
    (send memory store (+ address i)
          (bitwise-and (arithmetic-shift value (* -8 i)) #xff))))

(define semantic-samples
  (hash
   "store_byte_layout_writeback"
   (lambda ()
     (values
      (vector (mk 'str-full# '|| '|| '(2 1 4 0 1 0)))
      (progstate (vector 0 100 #x12345678 0 0 0 0 0 0 0 0 0 0 0 0 1000)
                 (progstate-memory (base-state))
                 0)
      '((reg 1) (mem 103))))
   "ldm_writeback_overridden"
   (lambda ()
     (define memory (progstate-memory (base-state)))
     (store-word-bytes! memory 100 #x11223344)
     (values
      (vector (mk 'ldm-full# '|| '|| '(3 8 0 1 1)))
      (progstate (vector 0 0 0 100 0 0 0 0 0 0 0 0 0 0 0 1000)
                 memory
                 0)
      '((reg 3))))
   "stm_store_old_base"
   (lambda ()
     (values
      (vector (mk 'stm-full# '|| '|| '(3 5 1 0 1)))
      (progstate (vector 11 22 33 100 0 0 0 0 0 0 0 0 0 0 0 1000)
                 (progstate-memory (base-state))
                 0)
      '((reg 3) (mem 92) (mem 96))))
   "pc_read_after_independent_add"
   (lambda ()
     (values
      (vector
       (mk 'add '|| '|| '(1 1 0))
       (mk 'add '|| '|| '(2 2 15)))
      (progstate (vector 5 10 20 0 0 0 0 0 0 0 0 0 0 0 0 1000)
                 (progstate-memory (base-state))
                 0)
      '((reg 2))))
   "pc_read_before_independent_add"
   (lambda ()
     (values
      (vector
       (mk 'add '|| '|| '(2 2 15))
       (mk 'add '|| '|| '(1 1 0)))
      (progstate (vector 5 10 20 0 0 0 0 0 0 0 0 0 0 0 0 1000)
                 (progstate-memory (base-state))
                 0)
      '((reg 2))))))

(define (emit-samples)
  (for ([sample samples])
    (match-define (list name rust-name rust-form my-inst) sample)
    (printf "~a ~a ~a ~a\n" name rust-name rust-form (hex32 (arm-inst->word machine my-inst)))))

(define (run-semantic-sample name)
  (define thunk (hash-ref semantic-samples name #f))
  (unless thunk
    (raise-user-error 'arm32-parity-cli "unknown semantic sample: ~a" name))
  (define-values (code state observations) (thunk))
  (define out (send simulator interpret code state))
  (for ([observation observations])
    (match observation
      [`(reg ,reg-id)
       (printf "reg ~a ~a\n" reg-id (vector-ref (progstate-regs out) reg-id))]
      [`(mem ,addr)
       (printf "mem ~a ~a\n" addr (send (progstate-memory out) lookup-update addr))])))

(match (current-command-line-arguments)
  [(vector "encode" op cond shf args ...)
   (encode-line (parse-symbol op)
                (parse-symbol cond)
                (parse-symbol shf)
                (map parse-arg args))]
  [(vector "parse-asm" line)
   (parse-asm-line line)]
  [(vector "parse-asm-batch")
   (parse-asm-batch)]
  [(vector "print-encoded" op cond shf args ...)
   (print-encoded-line (parse-symbol op)
                       (parse-symbol cond)
                       (parse-symbol shf)
                       (map parse-arg args))]
  [(vector "print-encoded-batch")
   (print-encoded-batch)]
  [(vector "surface-batch")
   (surface-batch)]
  [(vector "samples")
   (emit-samples)]
  [(vector "run-sample" name)
   (run-semantic-sample name)]
  [_
   (raise-user-error 'arm32-parity-cli
                     "usage: racket arm32-parity-cli.rkt encode <op> <cond> <shf> [args...] | parse-asm <line> | parse-asm-batch | print-encoded <op> <cond> <shf> [args...] | print-encoded-batch | surface-batch | samples | run-sample <name>")])
