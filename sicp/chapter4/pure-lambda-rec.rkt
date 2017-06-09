#lang racket

(provide factorial even?)

(define factorial
  (λ (n) ((λ (fact) (fact fact n))
           (λ (self k) (if (<= k 1) 1 (* k (self self (- k 1))))))))

(define even?
  (λ (x) ((λ (e? o?) (e? e? o? x))
           (λ (e? o? n) (if (= n 0) true (o? e? o? (- n 1))))
           (λ (e? o? n) (if (= n 0) false (e? e? o? (- n 1)))))))
