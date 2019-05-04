#lang racket

(provide (all-defined-out))

(define (end-cont)
  (λ (val) (printf "End of computation: ~a" val) val)
)

(define (apply-cont cont v) (cont v))
