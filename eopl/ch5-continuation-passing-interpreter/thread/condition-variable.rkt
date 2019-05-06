#lang racket

(provide (all-defined-out))

(require data/queue)
(require "scheduler.rkt")
(require "mutex.rkt")
(require "thread.rkt")

(struct condition-variable (mutex wait-queue))

(define (make-cond-var mutex)
  (condition-variable mutex (make-queue))
)

(define (cv-wait! cond-var thread)
  (match cond-var ((condition-variable mutex wait-queue)
    (mutex-unlock! mutex)
    (enqueue! wait-queue thread)
    (run-next-thread)
  ))
)

(define (cv-notify! cond-var)
  (match cond-var ((condition-variable mutex wait-queue)
    (unless (queue-empty? wait-queue)
      (let ((next-thread (dequeue! wait-queue)))
        (add-to-ready-queue!
          (thread
            (thread-id next-thread)
            (λ () (mutex-lock! mutex next-thread))))
      )
    )
  ))
)
