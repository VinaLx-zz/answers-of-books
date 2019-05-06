#lang racket

(provide (all-defined-out))

; ex 5.53. thread identifier
(define thread-id? integer?)

(struct thread (id cont))

(define main-thread-id 0)

(define next-id 1)
(define (new-thread-id!)
  (begin0 next-id (set! next-id (add1 next-id)))
)

(define/match (run-thread t)
  (((thread id cont)) (cont))
)
