#lang racket/base

(provide f-rec f-iter)

(define (f-rec n)
  (if (< n 3) n
    (+ (f-rec (- n 1)) (* (f-rec (- n 2)) 2) (* (f-rec (- n 3)) 3))))

(define (f-iter n) 
  (define (f-iter-impl f-3 f-2 f-1 n)
    (if (< n 0) f-1
      (f-iter-impl f-2 f-1 (+ f-1 (* 2 f-2) (* 3 f-3)) (- n 1))))
  (if (< n 3) n
    (f-iter-impl 0 1 2 (- n 3))))
