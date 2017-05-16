#lang racket

(provide accumulate-rec accumulate-iter)

(define (accumulate-rec combiner zero f a next b)
  (if (> a b) zero
      (combiner (f a) (accumulate-rec combiner zero f (next a) next b))))

(define (accumulate-iter combiner zero f a next b)
  (define (impl now acc)
    (if (> a b) acc
        (impl (next now) (combiner (f a) acc))))
  (impl a zero))

(define (sum-with-accumulate f a next b)
  (accumulate-iter + 0 f a next b))

(define (product-with-accumulate f a next b)
  (accumulate-iter * 1 f a next b))
