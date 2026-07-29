#lang racket

(require rosette
         rosette/solver/kodkod/kodkod
         rosette/solver/smt/z3)

(provide normalize-solver-name
         set-current-solver!)

(define (normalize-solver-name solver-name)
  (define name
    (cond
     [(symbol? solver-name) solver-name]
     [(string? solver-name) (string->symbol solver-name)]
     [else
      (raise-user-error 'normalize-solver-name
                        "expected solver name 'kodkod or 'z3, got ~a"
                        solver-name)]))
  (case name
    [(kodkod z3) name]
    [else
     (raise-user-error 'normalize-solver-name
                       "unsupported solver ~a; expected 'kodkod or 'z3"
                       solver-name)]))

(define (set-current-solver! solver-name)
  (case (normalize-solver-name solver-name)
    [(kodkod) (current-solver (new kodkod%))]
    [(z3) (current-solver (new z3%))]))
