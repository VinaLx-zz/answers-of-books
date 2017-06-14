#lang racket

(require "./compiler.rkt")
(require "./register-machine.rkt")
(require "../chapter4/eval.rkt")

(define datum
  '(begin
     (define (fact-iter n)
       (define (iter product counter)
         (if (> counter n) product
         (iter (* counter product) (+ counter 1))))
     (iter 1 1))
     (fact-iter 6)))

(define machine-ops
  (list
    (list 'lookup-variable-value lookup-variable-value)
    (list 'set-variable-value! set-variable-value!)
    (list 'define-variable define-variable!)
    (list 'exp-false? exp-false?)
    (list 'make-compiled-procedure make-compiled-procedure)
    (list 'compiled-procedure-env compiled-procedure-env)
    (list 'compiled-procedure-entry compiled-procedure-entry)
    (list 'extend-environment extend-environment)
    (list 'apply-primitive-procedure apply-primitive-procedure)
    (list 'list list)
    (list 'cons cons)
    (list 'printf printf)
    (list 'primitive-procedure? primitive-procedure?)
    (list 'setup-environment setup-environment)))

(define entry-code
  '(extern-entry
     (assign env (op setup-environment))
     (assign continue (label print-result))
     (perform (op printf) (const "~a\n") (reg env))
     (goto (reg val))
    print-result
     (perform (op printf) (const "[MACHINE-RESULT] ~a\n") (reg val))
    end))

(define registers '(val env argl proc continue))

(define (make-compiled-machine code)
  (let* ([machine (make-machine registers machine-ops entry-code)]
         [assembly (statements (my-compile code 'val 'return))]
         [machine-code (assemble assembly machine)])
    ; (show-code assembly)
    (machine 'trace-on)
    (set-register-contents! machine 'val machine-code)
    machine))

(define (show-code codes)
  (for-each
    (λ (code)
      (unless (symbol? code) (display "  "))
      (displayln code))
    codes))

; (show-code (statements (my-compile datum 'val 'next)))

(define machine (make-compiled-machine datum))
(start machine)
