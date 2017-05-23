#lang racket

(require (file "derivative.rkt"))
(provide (all-defined-out))

(define (deriv expression var)
  (let*-values (((prefix-expression ignore) (infix->prefix expression))
                ((deriv) (derivative prefix-expression var)))
    (prefix->infix deriv)))

(define (infix->prefix expression)
 (let-values (((lhs tail) (parse-primary expression)))
   (parse-impl tail lhs 0)))

(define (parse-primary expression)
  (let ((target (first expression)))
    (if (or (number? target) (symbol? target)) (values target (rest expression))
      (let-values (((res ignore) (infix->prefix target)))
        (values res (rest expression))))))

(define (parse-impl expression lhs min-prec)
  (if (empty? expression) (values lhs expression) 
   (let ((op (first expression)))
    (if (< (precedence op) min-prec) (values lhs expression)
        (let*-values (((rhs tail) (parse-primary (rest expression)))
                      ((rhs-ack tail2) (climb op rhs tail)))
          (parse-impl tail2 (list op lhs rhs-ack) min-prec))))))

(define (climb op rhs tail)
  (if (empty? tail) (values rhs tail)
    (let ((look-ahead-prec (precedence (first tail))))
        (if (<= look-ahead-prec (precedence op)) (values rhs tail)
        (let-values (((res tail2) (parse-impl tail rhs look-ahead-prec)))
        (climb op res tail2))))))

(define (prefix->infix expression)
  (prefix->infix-impl expression 0))

(define (prefix->infix-impl expression last-prec)
  (if (or (number? expression) (symbol? expression)) (list expression)
    (let* ((op (first expression))
           (op-prec (precedence op))
           (x (prefix->infix-impl (expr-lhs expression) op-prec))
           (y (prefix->infix-impl (expr-rhs expression) op-prec))
           (res (append x (list* op y))))
      (if (< op-prec last-prec) `(,res) res))))

(define expr-lhs cadr)
(define expr-rhs caddr)

(define (precedence op)
  (case op
    ((+ -) 1)
    ((/ *) 2)
    ((**) 3)
    ((eof) -1)
    (else (error 'precedence "invalid operator ~a" op))))
