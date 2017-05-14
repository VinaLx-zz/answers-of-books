#lang racket/base

(provide my-cube-root)

(define (my-cube-root x) (cube-root-iter 0 1.0 x))

(define (cube-root-iter last-guess guess x)
 (if (good-enough? last-guess guess 0.0001)
  guess
  (cube-root-iter guess (improve guess x) x)))

(define (good-enough? last-guess guess threshold)
 (< (abs (- last-guess guess)) threshold))

(define (improve guess x)
 (/ (+
     (/ x (square guess))
     (* 2 guess))
  3))

(define (average x y)
 (/ (+ x y) 2))

(define (square x) (* x x))
