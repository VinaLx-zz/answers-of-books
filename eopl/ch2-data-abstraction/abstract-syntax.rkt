#lang racket

(provide (all-defined-out))
(require (only-in eopl define-datatype cases))

(module tradictional-lc racket
  (provide (all-defined-out))
  (require (only-in eopl define-datatype cases))

  (define-datatype lc-exp lc-exp?
    (var-exp (var symbol?))
    (lambda-exp (bound-var symbol?) (body lc-exp?))
    (app-exp (rator lc-exp?) (rand lc-exp?))
  )

  ; identifier
  ; proc identifier => lc-exp
  ; lc-exp (lc-exp)
  ; ex 2.28. unparse lambda expression
  (define (unparse lam)
    (cases lc-exp lam
      (var-exp (var) (symbol->string var))
      (lambda-exp (var body)
        (format "proc ~a => ~a" var (unparse body)))
      (app-exp (op arg) (let
        ((op-str
          (cases lc-exp op
            (var-exp (var) (unparse op))
            (lambda-exp (p b) (format "(~a)" (unparse op)))
            (app-exp (op2 arg2) (unparse op))
          )
        ))
        (format "~a(~a)" op-str (unparse arg))
      ))
    )
  )

  ; ex 2.30. expressive error message for parser
  (define (parse-expression datum)
    (define (invalid-expression type datum)
      (error 'parse-expression "invalid ~a: ~a" type datum)
    )
    (define (parse-abstraction datum)
      (if (not (equal? (length datum) 3))
        (invalid-expression "lambda abstraction" datum)
        (lambda-exp (cadr datum) (parse-expression (caddr datum)))
      )
    )
    (define (parse-application datum)
      (if (not (equal? (length datum) 2))
        (invalid-expression "lambda application" datum)
        (app-exp
          (parse-expression (car datum)) 
          (parse-expression (cadr datum)))
      )
    )
    (cond
      ((symbol? datum) (var-exp datum))
      ((pair? datum)
        (if (equal? (car datum) 'lambda)
          (parse-abstraction datum)
          (parse-application datum)
        )
      )
      (else (invalid-expression "lambda expression" datum))
    )
  )
)

(require 'tradictional-lc)
(provide (all-from-out 'tradictional-lc))

; ex 2.29 parser for multi parameter lambda expression
(module* multi-param-lc #f
  (define (list-of pred) (λ (l) (andmap pred l)))
  (define-datatype lc-exp lc-exp?
    (var-exp (var symbol?))
    (lambda-exp (bound-var (list-of symbol?)) (body lc-exp?))
    (app-exp (rator lc-exp?) (rands (list-of lc-exp?)))
  )


  (define (parse-expression datum)
    (define (invalid-expression datum)
      (error 'parse-expression "invalid expression ~a" datum)
    )
    (define (parse-abstraction datum)
      (if (not (equal? (length datum) 3))
        (invalid-expression datum)
        (lambda-exp (cadr datum) (parse-expression (caddr datum)))
      )
    )
    (define (parse-application datum)
      (app-exp
        (parse-expression (car datum)) 
        (map parse-expression (cdr datum)))
    )
    (cond
      ((symbol? datum) (var-exp datum))
      ((pair? datum)
        (if (equal? (car datum) 'lambda)
          (parse-abstraction datum)
          (parse-application datum)
        )
      )
      (else (invalid-expression datum))
    )
  )
)

; ex 2.31. prefix-exp
(define-datatype prefix-exp prefix-exp?
  (const-exp (num integer?))
  (diff-exp (operand1 prefix-exp?) (operand2 prefix-exp?))
)
(define (parse-prefix-list l)
  (define (parse-prefix-list-impl l)
    (if (null? l)
      (error 'parse-prefix-list "incomplete prefix expression")
      (cond
        ((integer? (car l)) (values (const-exp (car l)) (cdr l)))
        ((equal? (car l) '-)
          (let*-values
            ( ((lexpr l1) (parse-prefix-list-impl (cdr l)))
              ((rexpr l2) (parse-prefix-list-impl l1)))
            (values (diff-exp lexpr rexpr) l2)
          ))
      )
    )
  )
  (let-values (((expr rest) (parse-prefix-list-impl l)))
    (if (cons? rest)
      (error 'parse-prefix-list
        "non-exhausted parse of ~a with ~a left" rest)
      expr
    )
  )
)
