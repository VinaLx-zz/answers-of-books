#lang racket

(provide (all-defined-out))

(define (my-cons x y) (λ (m) (m x y)))
(define (my-car p) (p (λ (x y) x)))
(define (my-cdr p) (p (λ (x y) y)))
