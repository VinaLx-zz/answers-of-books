#lang racket

(require data/queue)
(require "scheduler.rkt")

(provide (all-defined-out))

(struct mutex (locked wait-queue) #:mutable #:transparent)

(define (new-mutex)
  (mutex #f (make-queue))
)

(define (mutex-lock! mtx thread)
  (match mtx ((mutex locked wait-queue)
    (if locked
      (begin
        (enqueue! wait-queue thread)
        (run-next-thread)
      )
      (begin
        (set-mutex-locked! mtx #t)
        (thread)
      )
    )
  ))
)

(define (mutex-unlock! mtx)
  (match mtx ((mutex locked wait-queue)
    (if (queue-empty? wait-queue)
      (set-mutex-locked! mtx #f)
      (add-to-ready-queue! (dequeue! wait-queue))
    )
  ))
)
