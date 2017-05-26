#lang racket

(provide make-account)

(define (make-account balance password)
  (define (deposit number) (set! balance (+ balance number)) balance)
  (define (withdraw number) (if (> number balance) "not enough money"
                              (begin (set! balance (- balance number)) balance)))
  (let ((incorrect-pass 0)
        (frozen false))
    (λ (pass action number)
      (if frozen "account is frozen"
        (begin (set! incorrect-pass 0)
          (cond ((not (eq? pass password))
                   (set! incorrect-pass (add1 incorrect-pass))
                   (if (>= incorrect-pass 3)
                     (begin (set! frozen true) "invalid password, freeze the account")
                     "invalid password"))
                ((eq? action 'deposit) (deposit number))
                ((eq? action 'withdraw) (withdraw number))
                (else "invalid command")))))))
