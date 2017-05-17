#lang racket

(provide fixed-point fixed-point-sqrt fixed-point-cube-root) 

(define tolerence 0.00001)
(define (average v1 v2) (/ (+ v1 v2) 2))

(define (fixed-point f first-guess)
  (define (close-enough? v1 v2) (< (abs (- v1 v2)) tolerence))
  (define (try guess)
    (let ((next (f guess)))
       (if (close-enough? guess next) next (try next))))
  (try first-guess))

(define (fixed-point-of-transform f trans guess)
  (fixed-point (trans f) guess))

(define (average-damp f) (λ (x) (average x (f x))))

(define (fixed-point-sqrt x)
  (fixed-point-of-transform
    (λ (y) (/ x y) average-damp 1.0)))

(define (fixed-point-cube-root x)
  (fixed-point-of-transform
    (λ (y) (/ x (* y y) average-damp 1.0))))
