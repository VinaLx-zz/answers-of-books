#lang racket

(provide (all-defined-out))

(define zero (λ (f) (λ (x) x)))
(define (succ n) (λ (f) (λ (x) (f ((n f) x)))))
(define (plus m n) (λ (f) (λ (x) ((m f) ((n f) x)))))
(define (multiply m n) (λ (f) (λ (x) ((m (n f)) x))))
(define (exponent m n) (λ (f) (λ (x) (((m n) f) x))))

(define a (succ zero))
(define b (succ a))
(define c (plus a b))
(define d (multiply b c))
(define (add1 n) (printf "called by ~a\n" n) (+ 1 n))
(define (show x) ((x add1) 0))

