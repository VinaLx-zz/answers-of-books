#lang racket

(provide my-eval)

(define (my-eval expr env)
  (cond ((self-evaluating? expr) expr)
        ((variable? expr) (lookup-variable-value expr env))
        ((quoted? expr) (text-of-quotation expr))
        ((assignment? expr) (eval-assignment expr env))
        ((definition? expr) (eval-definition expr env))
        ((if-statement? expr) (eval-if expr env))
        ((lambda-expr? expr)
          (make-procedure (lambda-parameters expr)
                          (lambda-body expr)
                          env))
        ((begin-statement? expr)
          (eval-sequence (begin-actions expr) env))
        ((cond-statement? expr)
          (my-eval (cond->if expr) env))
        ((application? expr)
          (my-apply (my-eval (operator expr) env)
                    (list-of-values (operands expr) env)))
        ((and-statement? expr) (eval-and expr))
        ((or-statement? expr) (eval-or expr))
        (else (error 'my-eval "unknown expr: %a" expr))))

(define (my-apply procedure arguments)
  (cond ((primitive-procedure? procedure)
          (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
          (eval-sequence
            (procedure-body procedure)
            (extend-environment
              (procedure-arguments procedure)
              arguments
              (procedure-environment procedure))))
        (else (error 'my-apply "unknown procedure ~a" procedure))))

(define (list-of-values exps env)
  (if (no-operands? exps) empty
    (let ((first-value (my-eval (first-operand exps) env)))
      (cons first-value (list-of-values (rest-operand exps) env)))))

(define (eval-if expr env)
  (if (exp-true? (my-eval (if-predicate expr) env))
    (my-eval (if-consequent expr) env)
    (my-eval (if-alternative expr) env)))

(define (eval-sequence exps env)
  (let ((cur (my-eval (first-exp exps))))
    (if (last-exp? exps) cur
      (eval-sequence (rest-exps exps) env))))

(define (eval-assignment expr env)
  (set-variable-value! (assignment-variable expr)
                       (my-eval (assignment-value expr) env)
                       env)
  'ok)

(define (eval-definition expr env)
  (define-variable! (definition-variable expr)
                    (eval (definition-value expr) env)
                    env)
  'ok)

(define (self-evaluating? expr)
  (or (number? expr) (string? expr)))

(define variable? symbol?)

(define quoted? (tagged-list? 'quote))
(define text-of-quotation cadr)

(define ((tagged-list? tag) expr)
  (and (pair? expr) (eq? (car expr) tag)))

(define assignment? (tagged-list? 'set!))
(define assignment-variable cadr)
(define assignment-value caddr)

(define definition? (tagged-list? 'define))
(define (definition-variable expr)
  (if (symbol? (cadr expr)) (cadr expr) (caadr expr)))
(define (definition-value expr)
  (if (symbol? (cadr expr)) (caddr expr)
    (make-lambda (cdadr expr) (cddr expr))))

(define if-statement? (tagged-list? 'if))
(define if-predicate cadr)
(define if-consequent caddr)
(define (if-alternative expr)
  (if (not (empty? (cdddr expr))) (cadddr expr) 'false))
(define (make-if pred consequent alternative)
  (list 'if pred consequent alternative))

(define begin-statement? (tagged-list? 'begin))
(define begin-actions cdr)

(define (last-exp? seq) (empty? (cdr seq)))
(define first-exp car)
(define rest-exp cdr)

(define (sequence->expr seq)
  (cond ((empty? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))
(define (make-begin seq) (cons 'begin seq))

(define application? pair?)
(define operator car)
(define operands cdr)
(define no-operands? empty?)
(define first-operand car)
(define rest-operand cdr)

(define cond-statement? (tagged-list? 'cond))
(define cond-clauses cdr)
(define (cond-else-clauses? clause)
  (eq? (cond-predicate clause) 'else))
(define cond-predicate car)
(define cond-actions cdr)
(define (cond->if expr) (expand-clauses (cond-clauses expr)))
(define (expand-clauses clauses)
  (if (null? clauses) 'false
    (let* ((first-clause (car clauses))
           (rest-clauses (cdr clauses))
           (first-action (cond-actions first-clause)))
      (if (cond-else-clauses? first-clause)
        (if (empty? rest-clauses)
          (sequence->expr first-action)
          (error 'cond->if "else clause isn't last"))
        (make-if (cond-predicate first) (sequence->expr first-action)
          (expand-clauses rest-clauses))))))

(define and-statement? (tagged-list? 'and))
(define or-statement? (tagged-list? 'or))
(define (eval-and expr)
  (define (eval-and-impl exprs)
    (if (empty? exprs) true
      (if (exp-true? (my-eval (car exprs)))
        (eval-and-impl (cdr exprs))
        false)))
  (eval-and-impl (cdr expr)))
(define (eval-or expr)
  (define (eval-or-impl exprs)
    (if (empty? exprs) false
      (if (exp-true? (my-eval (car exprs)) true)
        (eval-or-impl (cdr exprs)))))
  (eval-or-impl (cdr expr)))

(define (exp-true? x) (not (eq? x false)))
(define (exp-false? x) (eq? x false))
