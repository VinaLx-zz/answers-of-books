#lang racket

(provide make-monitor)

(define (make-monitor f)
  (let ((counter 0))
    (λ args
      (if (eq? (first args) 'how-many-calls) counter
        (begin0 (apply f args) (set! counter (add1 counter)))))))
