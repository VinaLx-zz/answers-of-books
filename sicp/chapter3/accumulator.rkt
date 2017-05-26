#lang racket

(provide make-accumulator)

(define (make-accumulator zero)
 (λ (num) (set! zero (+ zero num)) zero))
