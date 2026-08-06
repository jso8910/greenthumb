#lang racket

(require rackunit
         racket/file
         "../arm-simulator-racket.rkt"
         "../arm-machine.rkt"
         "../arm-parser.rkt"
         "../arm-printer.rkt"
         "../arm-restrictions.rkt")

(define parser (new arm-parser%))

(define (encoded-inst asm [config 4])
  (define machine (new arm-machine% [config config]))
  (define printer (new arm-printer% [machine machine]))
  (values machine
          (vector-ref (send printer encode (send parser ir-from-string asm)) 0)))

(define (inst-word asm [config 4])
  (define-values (machine my-inst) (encoded-inst asm config))
  (arm-inst->word machine my-inst))

(check-equal? (inst-word "mov r0, #2\n") #xe3a00002)
(check-equal? (inst-word "add r0, r1, r2\n") #xe0810002)
(check-equal? (inst-word "add r0, r1, #2\n") #xe2810002)
(check-equal? (inst-word "movcc r0, r1\n") #x31a00001)
(check-equal? (inst-word "lsl r0, r1, r2\n") #xe1a00211)
(check-equal? (inst-word "asr r0, r1, #3\n") #xe1a001c1)
(check-equal? (inst-word "mul r0, r1, r2\n") #xe0000291)
(check-equal? (inst-word "smmul r0, r1, r2\n") #xe750f211)
(check-equal? (inst-word "sdiv r0, r1, r2\n") #xe710f211)
(check-equal? (inst-word "bfi r0, r1, #2, #5\n") #xe7c60111)
(check-equal? (inst-word "sbfx r0, r1, #2, #5\n") #xe7a40151)
(check-equal? (inst-word "rev r0, r1\n") #xe6bf0f31)
(check-equal? (inst-word "clz r0, r1\n") #xe16f0f11)
(check-equal? (inst-word "ldr r0, [r1, #4]\n") #xe5910004)
(check-equal? (inst-word "str r0, [r1, #-4]\n") #xe5010004)
(check-equal? (inst-word "cmp r0, #2\n") #xe3500002)
(check-equal? (inst-word "tst r0, r1\n") #xe1100001)

(define (with-restriction contents thunk)
  (define dir (make-temporary-file "arm-restrict-~a" 'directory "/tmp"))
  (define file (build-path dir "restrict.rkt"))
  (dynamic-wind
    void
    (lambda ()
      (call-with-output-file file #:exists 'truncate
        (lambda (out) (display contents out)))
      (thunk file))
    (lambda () (delete-directory/files dir #:must-exist? #f))))

(with-restriction
 "((default allow)
   (deny \"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx1x\"))"
 (lambda (file)
   (define machine (new arm-machine% [config 2]))
   (define printer (new arm-printer% [machine machine]))
   (send machine load-restrictions! file)
	   (define mov2 (send printer encode (send parser ir-from-string "mov r0, #2\n")))
	   (define mov1 (send printer encode (send parser ir-from-string "mov r0, #1\n")))
	   (check-false (send machine program-allowed? mov2))
	   (check-true (send machine program-allowed? mov1))))

(with-restriction
 "((default allow)
   (deny \"xxxxxxxxxxxxxxxxxxxxxxxxxxxxxx1x\"))"
 (lambda (file)
   (define machine (new arm-machine% [config 2]))
   (define printer (new arm-printer% [machine machine]))
   (send machine load-restrictions! file)
   (define mov170 (send printer encode (send parser ir-from-string "mov r0, #170\n")))
   (define mov340 (send printer encode (send parser ir-from-string "mov r0, #340\n")))
   (define mov257 (send printer encode (send parser ir-from-string "mov r0, #257\n")))
   (check-false (send machine program-allowed? mov170))
   (check-true (send machine program-allowed? mov340))
   (check-false (send machine program-allowed? mov257))))

(with-restriction
 "((default deny)
   (allow \"111000111010xxxxxxxxxxxxxxxxxxxx\"))"
 (lambda (file)
   (define machine (new arm-machine% [config 2]))
   (define printer (new arm-printer% [machine machine]))
   (send machine load-restrictions! file)
   (define mov2 (send printer encode (send parser ir-from-string "mov r0, #2\n")))
   (define add (send printer encode (send parser ir-from-string "add r0, r0, #1\n")))
   (check-true (send machine program-allowed? mov2))
   (check-false (send machine program-allowed? add))))

(define no-sub-family-restrictions
  "((default allow)
   (deny \"xxxx00x0010xxxxxxxxxxxxxxxxxxxxx\")
   (deny \"xxxx00x0110xxxxxxxxxxxxxxxxxxxxx\")
   (deny \"xxxx00x0011xxxxxxxxxxxxxxxxxxxxx\")
   (deny \"xxxx00x0111xxxxxxxxxxxxxxxxxxxxx\")
   (deny \"xxxx00x1010xxxxxxxxxxxxxxxxxxxxx\"))")

(with-restriction
 no-sub-family-restrictions
 (lambda (file)
   (define machine (new arm-machine% [config 4]))
   (define printer (new arm-printer% [machine machine]))
   (send machine load-restrictions! file)

   (define sub (send printer encode (send parser ir-from-string "sub r0, r1, r2\n")))
   (define rsb (send printer encode (send parser ir-from-string "rsb r0, r1, r2\n")))
   (define cmp (send printer encode (send parser ir-from-string "cmp r1, r2\n")))
   (define replacement
     (send printer encode
           (send parser ir-from-string
                 "mvn r3, r2\nadd r0, r1, r3\nadd r0, r0, #1\n")))

   (check-false (send machine program-allowed? sub))
   (check-false (send machine restriction-word-allowed? #xe0c10002)) ; sbc r0, r1, r2
   (check-false (send machine program-allowed? rsb))
   (check-false (send machine restriction-word-allowed? #xe0e10002)) ; rsc r0, r1, r2
   (check-false (send machine program-allowed? cmp))
   (check-true (send machine program-allowed? replacement))

   (define simulator (new arm-simulator-racket% [machine machine]))
   (define base-state (send machine get-state (lambda (#:min [min #f] #:max [max #f] #:const [const #f]) 0)))
   (for ([regs (list (vector 0 5 3 0)
                     (vector 0 -7 11 0)
                     (vector 0 0 -1 0)
                     (vector 0 #x7fffffff 1 0))])
     (define input (progstate (vector-copy regs) (progstate-memory base-state) -1))
     (define sub-output (send simulator interpret sub input))
     (define replacement-output (send simulator interpret replacement input))
     (check-equal? (vector-ref (progstate-regs replacement-output) 0)
	                   (vector-ref (progstate-regs sub-output) 0)))))

(check-exn
 exn:fail?
 (lambda () (compile-arm-pattern "xxx")))

(check-exn
 exn:fail?
 (lambda () (compile-arm-pattern "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxz")))
