#lang racket

(provide cont-frac e tan-cf)

(define (cont-frac n d k)
  (define (cont-frac-impl i)
     (if (> i k) 0.0
         (/ (n i) (+ (d i) (cont-frac-impl (add1 i))))))
  (cont-frac-impl 1))

(define e
  (+ 2 (cont-frac
         (lambda (i) 1) 
         (lambda (i)
           (if (not (= (remainder i 3) 2)) 1
               (* (/ (add1 i) 3) 2)))
         1000)))

(define (tan-cf x)
  (cont-frac
    (lambda (i) (if (= i 1) x (* x x)))
    (lambda (i) (add1 (* (- i 1) 2)))
    1000))
