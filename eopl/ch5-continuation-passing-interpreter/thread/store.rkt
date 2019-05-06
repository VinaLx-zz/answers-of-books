#lang racket

(provide send-value receive-value initialize-thread-stores!)

(require racket/undefined)
(require data/queue)
(require "scheduler.rkt")
(require "thread.rkt")
(require "../cont.rkt")

(define stores undefined)

(define (initialize-thread-stores!)
  (set! stores (make-hash))
)

(define (get-store-for-thread tid)
  (hash-ref! stores tid (make-queue))
)

(define (send-value tid value)
  (let ((store (get-store-for-thread tid)))
    (if (queue? store)
      (enqueue! store value)
      (begin
        (add-to-ready-queue! (thread tid (λ () (apply-cont store value))))
        (hash-remove! stores tid)
      )
    )
  )
)
(define (receive-value cont)
  (let ((store (get-store-for-thread current-thread-id)))
    (if (queue-empty? store)
      (begin
        (hash-set! stores current-thread-id cont)
        (run-next-thread)
      )
      (apply-cont cont (dequeue! store))
    )
  )
)
