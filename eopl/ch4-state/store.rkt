#lang racket

; ex 4.9. constant access store

(provide (all-defined-out))

(define (empty-store) (make-immutable-hash))

(define reference? integer?)

(define (store-size store) (hash-count store))

(define (invalid-reference-error source store ref)
  (error source "invalid reference ~a to store ~a" ref store)
)

(define (newref store val)
  (define next-ref (store-size store))
  (values next-ref (hash-set store next-ref val))
)

(define (deref store ref)
  (if (>= ref (store-size store))
    (invalid-reference-error 'deref store ref)
    (hash-ref store ref)
  )
)

(define (setref store ref val)
  (unless (hash-ref store ref #f)
    (invalid-reference-error 'setref store ref)
  )
  (hash-set store ref val)
)

(module* global-mutable #f
  (provide
    reference? empty-store initialize-store! setref!
    (rename-out (global:newref newref) (global:deref deref)) 
  )

  (define store-instance #f)

  (define (initialize-store!) (set! store-instance (empty-store)))

  (define (setref! ref val)
    (set! store-instance (setref store-instance ref val))
  )

  (define (global:newref val)
    (define-values (next-ref new-store) (newref store-instance val))
    (set! store-instance new-store)
    next-ref
  )

  (define (global:deref ref) (deref store-instance ref))
)
