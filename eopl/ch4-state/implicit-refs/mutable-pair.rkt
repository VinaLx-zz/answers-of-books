#lang racket

(provide (all-defined-out))

(require "../../eopl.rkt")
(require (submod "../store.rkt" global-mutable))

(define mutable-pair? (cons-of reference? reference?))

(define (make-pair lhs rhs)
  (cons (newref lhs) (newref rhs))
)

(define (left p) (deref (car p)))
(define (right p) (deref (cdr p)))

(define (set-left  p val) (setref! (car p) val))
(define (set-right p val) (setref! (cdr p) val))

