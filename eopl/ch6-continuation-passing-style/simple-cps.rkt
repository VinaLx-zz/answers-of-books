#lang racket

(provide (all-defined-out))

; ex 6.4
(define (remove-first/k xs x cont)
  (match xs
    ((quote ()) (cont null))
    ((cons x1 xs1)
      (if (equal? x x1) (cont xs1)
        (remove-first/k xs1 x (λ (r) (cont (cons x1 r))))
      )
    )
  )
)
(define (remove-first xs x) (remove-first/k xs x identity))

(define (list-sum/k xs cont)
  (match xs
    ((quote ()) (cont 0))
    ((cons x xs1) (list-sum/k xs1 (λ (r) (cont (+ x r)))))
  )
)
(define (list-sum xs) (list-sum/k xs identity))

(define (subst/k xs x1 x2 cont)
  (match xs
    ((quote ()) (cont null))
    ((cons x xs1)
      (let ((after (if (equal? x x1) x2 x)))
        (subst/k xs1 x1 x2 (λ (r) (cont (cons after r))))
      )
    )
  )
)
(define (subst xs x1 x2) (subst/k xs x1 x2 identity))

; ex 6.10.
(define (list-sum-iter xs cont)
  (match xs
    ((quote ()) cont)
    ((cons x xs1) (list-sum-iter xs1 (+ x cont)))
  )
)
(define (list-sum2 xs) (list-sum-iter xs 0))

