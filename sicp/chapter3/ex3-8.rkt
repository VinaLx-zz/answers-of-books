#lang racket

(provide f)

(define enable true)
(define (f x)
  (if (or (= x 0) (not enable)) (begin (set! enable false) 0) 1))
