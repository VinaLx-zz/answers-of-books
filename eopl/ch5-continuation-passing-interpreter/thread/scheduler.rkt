#lang racket

(provide (all-defined-out))

(require racket/undefined)
(require data/queue)

(define ready-queue undefined)
(define final-answer undefined)
(define time-slice undefined)
(define remaining-time undefined)

(define (initialize-scheduler! quantum)
  (set! ready-queue (make-queue))
  (set! time-slice quantum)
  (set! remaining-time quantum)
)

(define (enqueue-thread! thread)
  (enqueue! ready-queue thread)
)

(define (run-next-thread)
  (if (queue-empty? ready-queue) final-answer
    (let ((thread (dequeue! ready-queue)))
      (set! remaining-time time-slice)
      (thread)
    )
  )
)

(define (set-final-answer! value) (set! final-answer value))

(define (time-expired?) (zero? remaining-time))

(define (decrement-timer!) (set! remaining-time (- remaining-time 1)))

