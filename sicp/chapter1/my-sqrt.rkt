#lang racket/base

(provide my-sqrt)

(define (my-sqrt x) (sqrt-iter 0 1.0 x))

(define (sqrt-iter last-guess guess x)
 (if (good-enough? last-guess guess 0.0001)
  guess
  (sqrt-iter guess (improve guess x) x)))
    
(define (good-enough? last-guess guess threshold)
 (< (abs (- last-guess guess)) threshold))

(define (improve guess x)
 (average guess (/ x guess)))

(define (average x y)
 (/ (+ x y) 2))

(define (square x) (* x x))
