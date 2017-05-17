#lang racket

(provide cubic double composition repeat smooth n-fold-smooth)

(define (cubic a b c d)
  (λ (x) (+ (* a (* x x x)) (* b (* x x)) (* c x) d)))

(define (double f) (λ (x) (f (f x))))

(define (composition f g) (λ (x) (f (g x))))

(define (repeat f n)
  (define (repeat-impl acc i)
    (if (< n 0) acc (repeat-impl (composition f acc (sub1 n)))))
  (repeat-impl identity n))

(define (smooth f)
  (let ((dx 0.00001))
    (λ (x) (/ (+ (f (- (x dx))) (f x) (f (+ x dx))) 3))))

(define (n-fold-smooth f n) ((repeat smooth n) f))

