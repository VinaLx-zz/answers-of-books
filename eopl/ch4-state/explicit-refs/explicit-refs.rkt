#lang racket

(require "explicit-refs-data.rkt")
(require "../../eopl.rkt")
(require (submod "../store.rkt" global-mutable))

(provide (all-defined-out))

(sllgen:define syntax-spec '(
  ; program
  (Program (Expression) a-program)

  ; basic expressions
  (Expression (number) Num)
  (Expression (identifier) Var)
  (Expression ("-" "(" Expression "," Expression ")") Diff)
  (Expression ("zero?" "(" Expression ")") Zero?)
  (Expression ("if" Expression "then" Expression "else" Expression) If)
  (Expression
    ("let" (arbno identifier "=" Expression) "in" Expression)
    Let)
  (Expression ("(" Expression (arbno Expression) ")") Call)
  (Expression
    ("proc" "(" (separated-list identifier ",") ")" Expression)
    Proc)

  ; explicit references
  (Expression ("newref" "(" Expression ")") Newref)
  (Expression ("deref" "(" Expression ")") Deref)
  (Expression ("setref" "(" Expression "," Expression ")") Setref)

  ; ex 4.10. begin
  (Expression ("begin" (separated-list Expression ";") "end") Begin_)
))

(sllgen:make-define-datatypes eopl:lex-spec syntax-spec)
(define parse (sllgen:make-string-parser eopl:lex-spec syntax-spec))

(define (value-of-program pgm)
  (cases Program pgm
    (a-program (expr)
      (initialize-store!)
      (expval->val (value-of expr (init-env)))
    )
  )
)

(define (value-of expr env)
  (define (eval e) (value-of e env))
  (cases Expression expr
    (Num (n) (num-val n))
    (Var (var) (apply-env env var))
    (Diff (lhs rhs)
      (num-val (- (expval->num (eval lhs)) (expval->num (eval rhs))))
    )

    (Zero? (expr) (bool-val (zero? (expval->num (eval expr)))))

    (If (test texpr fexpr)
      (if (expval->bool (eval test)) (eval texpr) (eval fexpr))
    )

    (Let (vars vals body)
      (let ((new-env
        (extend-env* vars (map eval vals) env)))
        (value-of body new-env)
      )
    )

    (Proc (params body) (make-procedure-val params body env))

    (Call (operator operands)
      (let ((proc (expval->proc (value-of operator env)))
            (args (map eval operands)))
        (apply-procedure proc args)
      )
    )

    ; explicit references
    (Newref (expr) (ref-val (newref (eval expr))))
    (Setref (lhs rhs)
      (setref! (expval->ref (eval lhs)) (eval rhs))
      (void-val)
    )
    (Deref (expr) (deref (expval->ref (eval expr))))

    ; ex 4.10.
    (Begin_ (exprs) (last (map eval exprs)))

    ; ex 4.11. list
    ; almost the same as `begin`, omitted

  ) ; cases
) ; value-of

(define (apply-procedure p args)
  (match p ((Procedure vars body env)
    (if (not (equal? (length args) (length vars)))
      (error 'apply-procedure
        "procedure arity mismatch between ~a (parameters) and ~a (arguments)"
        (length args) (length vars))
      (value-of body (extend-env* vars args env))
    )
  ))
)

((sllgen:make-rep-loop "sllgen> " value-of-program
   (sllgen:make-stream-parser eopl:lex-spec syntax-spec)))

; ex 4.12. ex 4.13.
;
; Straightforward implementation leads to laborious work in most of the time.
; So the sample codes are omitted.
