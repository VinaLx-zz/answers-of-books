#lang racket

(provide (all-defined-out))

(require racket/undefined)
(require data/queue)
(require "thread.rkt")

(define ready-queue undefined)
(define final-answer undefined)
(define max-quantum undefined)
(define remaining-time undefined)
(define current-thread-id undefined)

(define (initialize-scheduler! quantum)
  (set! ready-queue (make-queue))
  (set! max-quantum quantum)
  (set! remaining-time quantum)
  (set! current-thread-id main-thread-id)
)

; ex 5.46. record the quantum left for ready thread
(struct ready-thread (thread quantum))

(define (add-to-ready-queue! thread)
  (let ((quantum
         (if (zero? remaining-time) max-quantum remaining-time)))
    (enqueue! ready-queue (ready-thread thread quantum))
  )
)

(define (run-next-thread)
  (if (queue-empty? ready-queue) final-answer
    (match-let (((ready-thread thread quantum)
                 (dequeue! ready-queue)))
      (set! remaining-time quantum)
      (set! current-thread-id (thread-id thread))
      (run-thread thread)
    )
  )
)

(define (set-final-answer! value) (set! final-answer value))

(define (time-expired?) (zero? remaining-time))

(define (decrement-timer!) (set! remaining-time (- remaining-time 1)))

(define (wrap-current-thread body)
  (thread current-thread-id body)
)
(define (yield-current-thread body)
  (add-to-ready-queue! (wrap-current-thread body))
  (run-next-thread)
)

; ex 5.54. kill
(define (remove-from-ready! tid)
  (let ((length-before-filter (queue-length ready-queue)))
    (queue-filter! ready-queue (λ (t)
      (not (equal? (thread-id (ready-thread-thread t)) tid))
    ))
    (not (equal? length-before-filter (queue-length ready-queue)))
  )
)
