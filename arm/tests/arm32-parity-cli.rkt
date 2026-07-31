#lang racket

(require racket/format
         racket/match
         "../arm-machine.rkt"
         "../arm-restrictions.rkt"
         "../arm-simulator-racket.rkt"
         "../../inst.rkt")

(define machine (new arm-machine% [config 16]))
(define simulator (new arm-simulator-racket% [machine machine]))

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
      '((reg 3) (mem 92) (mem 96))))))

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
  [(vector "samples")
   (emit-samples)]
  [(vector "run-sample" name)
   (run-semantic-sample name)]
  [_
   (raise-user-error 'arm32-parity-cli
                     "usage: racket arm32-parity-cli.rkt encode <op> <cond> <shf> [args...] | samples | run-sample <name>")])
