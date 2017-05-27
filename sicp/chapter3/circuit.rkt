#lang racket

(provide (all-defined-out))

(define (get-signal wire) (wire 'get-signal))

(define (set-signal! wire new-value) ((wire 'set-signal!) new-value))

(define (add-action! wire callback) ((wire 'add-action!) callback))

(define (after-delay d callback) (callback))

(define (probe name wire)
  (add-action! wire
    (λ () (printf "name: ~a\nnew value: ~a\n"
            name (get-signal wire)))))

(define (inverter in out)
  (define inverter-delay 2)
  (define (invert-input)
    (let ((new-value (not (get-signal in))))
      (after-delay inverter-delay (λ () (set-signal! out new-value)))))
  (add-action! in invert-input) 'ok)

(define (and-gate in1 in2 out)
  (define and-gate-delay 3)
  (define (and-action)
    (let ((new-value (and (get-signal in1) (get-signal in2))))
      (after-delay and-gate-delay (λ () (set-signal! out new-value)))))
  (add-action! in1 and-action)
  (add-action! in2 and-action)
  'ok)

(define (or-gate in1 in2 out)
  (define or-gate-delay 5)
  (define (or-action)
    (let ((new-value (or (get-signal in1) (get-signal in2))))
      (after-delay or-gate-delay (λ () (set-signal! out new-value)))))
  (add-action! in1 or-action)
  (add-action! in2 or-action)
  'ok)

(define (make-wire)
  (let ((signal-value 0)
        (action-procedures empty))
    (define (set-my-signal! new-value)
      (if (not (equal? signal-value new-value))
        (begin (set! signal-value new-value)
               (for-each (λ (action) (action)) action-procedures))
        'done))
    (define (accept-action! f)
      (set! action-procedures (list* f action-procedures))
      (f))
    (define (dispatch m)
      (case m ((get-signal) signal-value)
              ((set-signal!) set-my-signal!)
              ((add-action!) accept-action!)
              (else (error `wire-dispatch "unknown operation ~a" m))))
    dispatch))
