#lang racket

(require "thread/scheduler.rkt")

(provide (all-defined-out))

(define (end-cont)
  (λ (val) (printf "End of computation: ~a\n" val) val)
)

(define (apply-cont cont v)
  (if (time-expired?)
    (begin
      (enqueue-thread! (λ () (apply-cont cont v)))
      (run-next-thread)
    )
    (begin
      (decrement-timer!)
      (cont v)
    )
  )
)

(define cont? procedure?)

(define end-main-thread
  (λ (val)
    (set-final-answer! val)
    (run-next-thread)
  )
)

(define end-subthread
  (λ (val)
    (run-next-thread)
  )
)

