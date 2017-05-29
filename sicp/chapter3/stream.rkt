#lang racket

(provide (all-defined-out))

; it doesn't work for racket for the strict evaluation model?
(define (cons-stream h t) (cons h (delay t)))

(define stream-car car)

(define (stream-cdr s) (force (cdr s)))

(define stream-null? null?)

(define empty-stream empty)

(define (stream-ref s n)
  (if (= n 0) (stream-car s)
    (stream-ref (stream-cdr s) (sub1 n))))

(define (stream-map f s)
  (if (stream-null? s) empty-stream
    (cons-stream (f (stream-car s))
                 (stream-map f (stream-cdr s)))))

(define (stream-for-each f s)
  (if (stream-null? s) (void)
    (begin (f (stream-car s))
      (stream-for-each f (stream-cdr s)))))

(define (stream-filter f s)
  (cond ((stream-null? s) empty-stream)
        ((f (stream-car s))
          (cons-stream (stream-car s)
                       (stream-filter f (stream-cdr s))))
        (else (stream-filter f (stream-cdr s)))))

(define (display-stream s)
  (define (display-stream-impl s)
    (if (stream-null? s) (void)
      (begin (printf " ~a" (stream-car s))
             (display-stream-impl (stream-cdr s)))))
  (display "stream(")
  (if (stream-null? s) (void)
    (begin (display (stream-car s))
           (display-stream-impl (stream-cdr s))))
  (display ")\n"))
