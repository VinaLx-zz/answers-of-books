#lang racket

(provide fast-power-rec fast-power-iter)

(define (square a) (* a a))
(define (even? n) (= (remainder n 2) 0))
(define (double n) (* n 2))

(define (fast-power-rec b n)
   (cond ((= n 0) 1)
         ((even? n) (square (fast-power-rec b (/ n 2))))
         (else (* b (fast-power-rec b (sub1 n))))))

(define (fast-power-iter b n)
  (define (fast-power-impl cur acc total multer)
    (let ((next (* 2 cur)))
         (cond ((= total 0) acc)
               ((<= next total) (fast-power-impl (double cur) acc total (square multer)))
               (else (fast-power-impl 1 (* acc multer) (- total cur) b)))))
  (fast-power-impl 1 1 n b))
