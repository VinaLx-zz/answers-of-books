#lang racket

(provide filtered-accumulate)

(define (filtered-accumulate combine filt zero f a next b)
  (if (> a b) zero
      (let ((now (if (filt a) (f a) zero)))
        (combine now
          (filtered-accumulate combine filt zero f (next a) next b)))))
