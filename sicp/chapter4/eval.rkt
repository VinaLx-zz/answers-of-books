#lang racket

(provide (all-defined-out))

(define (my-eval expr env)
  (cond [(self-evaluating? expr) expr]
        [(variable? expr) (lookup-variable-value expr env)]
        [(quoted? expr) (text-of-quotation expr)]
        [(assignment? expr) (eval-assignment expr env)]
        [(definition? expr) (eval-definition expr env)]
        [(if-statement? expr) (eval-if expr env)]
        [(lambda-expr? expr)
         (make-procedure (lambda-parameters expr)
                         (lambda-body expr)
                         env)]
        [(begin-statement? expr)
         (eval-sequence (begin-actions expr) env)]
        [(cond-statement? expr)
         (my-eval (cond->if expr) env)]
        [(and-statement? expr) (eval-and expr env)]
        [(or-statement? expr) (eval-or expr env)]
        [(application? expr)
         (my-apply (my-eval (operator expr) env)
                   (list-of-values (operands expr) env))]
        [else (error 'my-eval "unknown expr: ~a" expr)]))

(define (my-apply procedure arguments)
  (cond [(primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments)]
        [(compound-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (extend-environment
             (procedure-parameters procedure)
             arguments
             (procedure-environment procedure)))]
        [else (error 'my-apply "unknown procedure ~a" procedure)]))

(define (list-of-values exps env)
  (if (no-operands? exps) empty
    (let ((first-value (my-eval (first-operand exps) env)))
      (cons first-value (list-of-values (rest-operand exps) env)))))

(define (eval-if expr env)
  (if (exp-true? (my-eval (if-predicate expr) env))
    (my-eval (if-consequent expr) env)
    (my-eval (if-alternative expr) env)))

(define (eval-sequence exps env)
  (let ((cur (my-eval (first-exp exps) env)))
    (if (last-exp? exps) cur
      (eval-sequence (rest-exps exps) env))))

(define (eval-assignment expr env)
  (set-variable-value! (assignment-variable expr)
                       (my-eval (assignment-value expr) env)
                       env)
  'ok)

(define (eval-definition expr env)
  (define-variable! (definition-variable expr)
                    (my-eval (definition-value expr) env)
                    env)
  'ok)

(define (self-evaluating? expr)
  (or (number? expr) (string? expr)))

(define variable? symbol?)

(define ((tagged-list? tag) expr)
  (and (pair? expr) (eq? (car expr) tag)))

(define quoted? (tagged-list? 'quote))
(define text-of-quotation cadr)


(define assignment? (tagged-list? 'set!))
(define assignment-variable cadr)
(define assignment-value caddr)

(define definition? (tagged-list? 'define))
(define (definition-variable expr)
  (if (symbol? (cadr expr)) (cadr expr) (caadr expr)))
(define (definition-value expr)
  (if (symbol? (cadr expr)) (caddr expr)
    ; arguments and body
    (make-lambda (cdadr expr) (cddr expr))))

(define lambda-expr? (tagged-list? 'lambda))
(define lambda-parameters cadr)
(define lambda-body cddr)
(define (make-lambda params body)
  (cons 'lambda (cons params body)))

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
(define rest-exps cdr)

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
    (let* ([first-clause (car clauses)]
           [rest-clauses (cdr clauses)]
           [first-action (cond-actions first-clause)])
      (if (cond-else-clauses? first-clause)
        (if (empty? rest-clauses)
          (sequence->expr first-action)
          (error 'cond->if "else clause isn't last"))
        (make-if (cond-predicate first-clause) (sequence->expr first-action)
          (expand-clauses rest-clauses))))))

(define and-statement? (tagged-list? 'and))
(define or-statement? (tagged-list? 'or))

(define (eval-and expr env)
  (define (eval-and-impl exprs)
    (if (empty? exprs) true
      (if (exp-true? (my-eval (car exprs) env))
        (eval-and-impl (cdr exprs))
        false)))
  (eval-and-impl (cdr expr)))

(define (eval-or expr env)
  (define (eval-or-impl exprs)
    (if (empty? exprs) false
      (if (exp-true? (my-eval (car exprs) env)) true
        (eval-or-impl (cdr exprs)))))
  (eval-or-impl (cdr expr)))

(define (exp-true? x) (not (eq? x false)))
(define (exp-false? x) (eq? x false))

(define (apply-primitive-procedure f args)
  (apply (primitive-implementation f) args))

(define (make-procedure params body env)
  (list 'procedure params body env))
(define compound-procedure? (tagged-list? 'procedure))
(define procedure-parameters cadr)
(define procedure-body caddr)
(define procedure-environment cadddr)


(define enclosing-environment mcdr)
(define first-frame mcar)
(define empty-env empty)

(define (make-frame vars vals)
  (if (empty? vars) empty
    (cons (mcons (car vars) (car vals))
          (make-frame (cdr vars) (cdr vals)))))

(define (extend-environment vars vals env)
  (if (not (= (length vars) (length vals)))
    (error 'extend-environment "variable and value don't match!")
    (mcons (make-frame vars vals) env)))
    

(define (lookup-in-frames var frame)
  (if (empty? frame) false
    (let ((kv (car frame)))
      (if (eq? (mcar kv) var) kv
        (lookup-in-frames var (cdr frame))))))

(define (lookup-variable var env)
  (if (empty? env) false
    (let ((kv (lookup-in-frames var (first-frame env))))
      (if kv kv (lookup-variable var (mcdr env))))))

(define (lookup-variable-value var env)
  (let ((kv (lookup-variable var env)))
    (if kv (mcdr kv) (error 'lookup-variable "unbound variable ~a" var))))

(define (define-variable! var val env)
  (let* ((frame (first-frame env))
         (kv (lookup-in-frames var frame)))
    (if kv (set-mcdr! kv val)
      (set-mcar! env (cons (mcons var val) frame)))))

(define (set-variable-value! var val env)
  (let ((kv (lookup-variable var env)))
    (if kv (set-mcdr! kv val) (error 'set-variable "unbound variable ~a" var))))

(define primitive-procedures
  (list `(car ,car)
        `(cdr ,cdr)
        `(cons ,cons)
        `(null? ,null?)
        `(+ ,+)
        `(- ,-)
        `(* ,*)
        `(/ ,/)))

(define (primitive-procedure-names) (map car primitive-procedures))
(define (primitive-procedure-objects)
  (map (λ (f) (list 'primitive (cadr f)))
       primitive-procedures))

(define (setup-environment)
  (let ([initial
        (extend-environment
          (primitive-procedure-names)
          (primitive-procedure-objects)
          empty-env)])
    (define-variable! 'true true initial)
    (define-variable! 'false false initial)
    initial))
(define global-env (setup-environment))

(define primitive-procedure? (tagged-list? 'primitive))
(define primitive-implementation cadr)

(define input-prompt "my-eval> ")

(define (driver-loop)
  (display input-prompt)
  (let* ([input (read)])
    (if (eq? input eof) (void)
      (begin
        (displayln (my-eval input global-env))
        ; (displayln global-env)
        (driver-loop)))))

(driver-loop)
