#lang racket

(provide make-account make-joint)

(define (make-account balance password)
  (define (deposit number) (set! balance (+ balance number)) balance)
  (define (withdraw number) (if (> number balance) "not enough money"
                              (begin (set! balance (- balance number)) balance)))
  (define (dispatch action . args)
    (case action
      ((deposit) (apply deposit args))
      ((withdraw) (apply withdraw args))
      ((password) password)
      (else "unknown operation")))
  (make-general-account password
    (λ (action (number 0)) (dispatch action number))))

(define (password-keeper password (try 3))
  (let ((state 0))
    (λ (pass)
      (cond ((eq? state 'frozen) state)
            ((or (eq? password pass) (eq? password 'password)) (set! state 0) 'ok)
            (else (set! state (add1 state))
                  (if (>= state try) (begin (set! state 'frozen) state) state))))))

(define (account-validator keeper)
  (λ (password)
    (case (keeper password)
      ((frozen) "account is frozen")
      ((ok) 'ok)
      (else "invalid password"))))

(define (make-general-account password f)
  (let* ((pass-keeper (password-keeper password))
         (validator (account-validator pass-keeper)))
    (λ (pass . args)
      (let ((result (validator pass)))
        (if (eq? result 'ok) (apply f args) result)))))

(define (make-joint account password new-password)
  (make-general-account new-password
    (λ (action (number 0)) (account password action number))))
