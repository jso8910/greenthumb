#lang racket

(require rackunit
         "../../parallel-driver.rkt")

(check-false (two-phase-improvement-window 60 0 #f #f))
(check-equal? (two-phase-improvement-window 60 10 20 #f) 20)
(check-equal? (two-phase-improvement-window 60 20 #f 1/4) 10)
(check-equal? (two-phase-improvement-window 60 20 20 1/4) 10)
(check-equal? (two-phase-improvement-window "80" "40" "30" "1/4") 10)
(check-equal? (two-phase-improvement-window 60 60 20 1/4) 0)

(check-exn
 exn:fail?
 (lambda () (two-phase-improvement-window 60 0 -1 #f)))

(check-exn
 exn:fail?
 (lambda () (two-phase-improvement-window 60 0 #f "nope")))
