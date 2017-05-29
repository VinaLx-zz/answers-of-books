#lang racket

; I use the racket standard library implementation of stream here

(provide (all-defined-out))

; simple primitives that standard library lack

(define (stream-take s n)
  (if (<= n 0) empty-stream
    (stream-cons (stream-first s) (stream-take (stream-rest s) (sub1 n)))))

(define (display-stream s)
  (define (display-stream-impl s)
    (if (stream-empty? s) (void)
        (begin (printf ", ~a" (stream-first s))
            (display-stream-impl (stream-rest s)))))
  (display "stream(")
  (if (stream-empty? s) (void)
    (begin (display (stream-first s))
           (display-stream-impl (stream-rest s))))
  (display ")\n"))

(define (show s n) (display-stream (stream-take s n)))

(define (stream-map* f . ss)
  (if (ormap stream-empty? ss) empty-stream
    (stream-cons (apply f (map stream-first ss))
      (apply stream-map* (cons f (map stream-rest ss))))))

(define (stream-+ xs ys) (stream-map* + xs ys))
(define (stream-* xs ys) (stream-map* * xs ys))

(define (stream-merge xs ys (less-than <))
  (cond ((stream-empty? xs) ys)
        ((stream-empty? ys) xs)
        (else
          (let ((x (stream-first xs))
                (y (stream-first ys)))
            (if (less-than x y)
              (stream-cons x (stream-merge (stream-rest xs) ys less-than))
              (stream-cons y (stream-merge xs (stream-rest ys) less-than)))))))

(define (stream-unique s)
  (define (stream-unique-impl s memo)
    (if (stream-empty? s) empty-stream
      (let ((now (stream-first s)))
        (if (equal? now memo) (stream-unique-impl (stream-rest s) memo)
          (stream-cons now (stream-unique-impl (stream-rest s) now))))))
  (stream-unique-impl s 'no-element-would-be-equal-to-me))

(define (stream-interleave xs ys)
  (if (stream-empty? xs) ys
    (stream-cons (stream-first xs)
                 (stream-interleave ys (stream-rest xs)))))

(define (stream-pairs xs ys)
  (stream-cons (list (stream-first xs) (stream-first ys))
    (stream-interleave
      (stream-map (λ (y) (list (stream-first xs) y)) (stream-rest ys))
      (stream-pairs (stream-rest xs) (stream-rest ys)))))

(define (stream-pairs-merged xs ys less-than)
  (stream-cons (list (stream-first xs) (stream-first ys))
    (stream-merge
      (stream-map (λ (y) (list (stream-first xs) y)) (stream-rest ys))
      (stream-pairs-merged (stream-rest xs) (stream-rest ys) less-than)
      less-than)))

(define (triples xs ys zs)
  (define (triples-impl xs ys zs)
    (let ((rests (stream-pairs-merged ys zs pair-less-than))
          (now (stream-first xs)))
      (stream-cons (list now (stream-first rests))
        (stream-merge
          (stream-map (λ (p) (list now p)) (stream-rest rests))
          (triples-impl (stream-rest xs) (stream-rest ys) (stream-rest zs))
          triple-less-than))))
  (stream-map
    (match-lambda ((list x (list y z)) (list x y z)))
    (triples-impl xs ys zs)))

; then comes various infinite-stream

(define (constant n) (stream-cons n (constant n)))
(define (from n) (stream-cons n (from (add1 n))))

(define naturals (from 0))

(define (fibo-impl a b) (stream-cons a (fibo-impl b (+ a b))))
(define fibo (fibo-impl 0 1))

(define (powers n) (stream-cons 1 (stream-* (powers n) (constant n))))

(define (partial-sums s)
  (stream-cons (stream-first s)
    (stream-+ (stream-rest s) (partial-sums s))))

(define ugly-numbers
  (stream-unique
    (stream-cons 1 (stream-merge (stream-* ugly-numbers (constant 2))
      (stream-merge (stream-* ugly-numbers (constant 3))
        (stream-* ugly-numbers (constant 5)))))))

(define (expand n d r)
  (stream-cons (quotient (* n r) d)
    (expand (remainder (* n r) d) d r)))

(define (pi-series-terms n)
  (stream-cons (/ 1.0 n) (stream-map - (pi-series-terms (+ n 2)))))
(define pi-stream
  (stream-* (constant 4) (partial-sums (pi-series-terms 1))))

(define (square x)  (* x x))

(define (euler-trans s)
  (let ((s0 (stream-ref s 0))
        (s1 (stream-ref s 1))
        (s2 (stream-ref s 2)))
    (stream-cons (- s2 (/ (square (- s2 s1)) (+ s0 (* -2 s1) s2)))
      (euler-trans (stream-rest s)))))

(define (make-tableau trans s)
  (stream-cons s (make-tableau trans (trans s))))
(define (accelerate trans s)
  (stream-map stream-first (make-tableau trans s)))

(define pair-less-than (λ (p1 p2)
  (if (= (cadr p1) (cadr p2)) (< (car p1) (car p2))
    (< (cadr p1) (cadr p2)))))

(define natural-pairs
  (stream-pairs-merged naturals naturals pair-less-than))

(define (triple-less-than t1 t2)
  (if (equal? (cadr t1) (cadr t2)) (< (car t1) (car t2))
    (pair-less-than (cadr t1) (cadr t2))))

(define natural-triples (triples naturals naturals naturals))
