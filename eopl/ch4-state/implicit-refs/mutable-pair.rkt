#lang racket

(provide (all-defined-out))

(require "../../eopl.rkt")
(require (submod "../store.rkt" global-mutable))

(define mutable-pair? (cons-of reference? reference?))

(define (make-pair lhs rhs)
  (cons (newref lhs) (newref rhs))
)

(define (left p) (deref (car p)))
(define (right p) (deref (cdr p)))

(define (set-left  p val) (setref! (car p) val))
(define (set-right p val) (setref! (cdr p) val))


; ex 4.29. array
(struct array (length data) #:transparent)

(define (new-array l vals)
  (array l (map newref vals))
)
(define (array-get-ref arr n)
  (list-ref (array-data arr) n)
)

(define (array-ref arr n)
  (boundary-check 'array-ref arr n)
  (deref (array-get-ref arr n))
)

(define (array-set arr n val)
  (boundary-check 'array-set arr n)
  (setref! (array-get-ref arr n) val)
)

; ex 4.30. constant time array boundary check
(define (boundary-check source arr n)
  (when (or (< n 0) (>= n (array-length arr)))
    (error source "access out of bound of ~a with index ~a" arr n)
  )
)
