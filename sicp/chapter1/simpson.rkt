#lang racket

(provide simpson)

(define (simpson f a b n)
  (let ((h (/ (- b a) n)))
     (define (get-x i) (+ a (* i h)))
     (define (get-y i) (f (get-x i)))
     (define (simpson-impl acc i)
       (cond ((= i n) (/ (* h (+ acc (get-y i))) 3))
             ((odd? i) (simpson-impl (+ acc (* (get-y i) 4)) (add1 i)))
             (else (simpson-impl (+ acc (* (get-y i) 2)) (add1 i)))))
     (simpson-impl (get-y 0) 1)))
