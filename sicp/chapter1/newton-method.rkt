#lang racket

(require "fixed-point.rkt")

(provide newton-method)

(define (derivative f)
  (let ((dx 0.00001))
    (λ (x) (/ (- (f (+ x dx)) (f (- x dx))) (* 2 dx)))))

(define (newton-transform f)
  (λ (x) (- x (/ (f x) ((derivative f) x)))))

(define (newton-method f guess)
  (fixed-point (newton-transform f) guess))
