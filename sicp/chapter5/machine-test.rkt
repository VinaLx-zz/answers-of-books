#lang racket

(require "./register-machine.rkt")
(provide (all-defined-out))

(define gcd-machine
  (make-machine
    '(a b t)
    (list (list 'rem remainder) (list '= =))
    '(test-b
        (test (op =) (reg b) (const 0))
        (branch (label gcd-done))
        (assign t (op rem) (reg a) (reg b))
        (assign a (reg b))
        (assign b (reg t))
        (goto (label test-b))
        gcd-done)))

(define (machine-gcd a b)
  (set-register-contents! gcd-machine 'a a)
  (set-register-contents! gcd-machine 'b b)
  (start gcd-machine)
  (get-register-contents gcd-machine 'a))

(define fact-machine
  (make-machine
    '(n val continue)
    (list (list '= =) (list '* *) (list '- -))
    '(test-f
        (assign continue (label fact-done))
      fact-loop
        (test (op =) (reg n) (const 1))
        (branch (label base-case))
        (save continue)
        (save n)
        (assign n (op -) (reg n) (const 1))
        (assign continue (label after-fact))
        (goto (label fact-loop))
      after-fact
        (restore n)
        (restore continue)
        (assign val (op *) (reg n) (reg val))
        (goto (reg continue))
      base-case
        (assign val (const 1))
        (goto (reg continue))
        fact-done)))

(define (machine-fact n)
  (set-register-contents! fact-machine 'n n)
  (fact-machine 'trace-on)
  (start fact-machine)
  (get-register-contents fact-machine 'val))

(printf "~a\n" (machine-fact 6))

