#lang racket

(provide (all-defined-out) show)

(require "infinite-stream.rkt")

(define (sign-change-detector cur prev)
  (cond ((>= (* cur prev) 0) 0)
        ((< cur 0) -1)
        (else 1)))

(define (zero-crossings input-data)
  (stream-map* sign-change-detector input-data (stream-cons 0 input-data)))

(define test-input
  (stream 1 2 1.5 1 0.5 -0.1 -2 -3 -2 -0.5 0.2 3 4))

(define (integral xs s0 dt)
  (define result
    (stream-cons s0 (stream-+ (stream-* xs (constant dt)) result)))
  result)

(define (integral-delayed xs-delayed s0 dt)
  (define result
    (stream-cons s0
      (stream-+ (stream-* (force xs-delayed) (constant dt)) result)))
  result)

(define ((rlc r l c dt) v0 i0)
  (letrec ((il-int (integral-delayed (delay il) i0 dt))
           (vc-int (integral-delayed (delay vc) v0 dt))
           (vc (stream-map (λ (x) (/ (- x) c)) il-int))
           (il (stream-+
                 (stream-map (λ (v) (/ v l)) vc-int)
                 (stream-map (λ (i) (/ (* -1 r i) l)) il-int))))
    (cons vc il)))

(match-define (cons vc il) ((rlc 1.0 0.2 1.0 0.1) 10.0 0.0 ))
