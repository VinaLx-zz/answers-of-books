#lang racket

(provide sum-rec sum-iter)

(define (sum-rec f a next b)
  (if (> a b) 0
      (+ (f a) (sum-rec f (next a) next b))))

(define (sum-iter f a next b)
  (define (impl now acc)
     (if (> now b) acc
         (impl (next now) (+ acc (f now)))))
  (impl a 0))
