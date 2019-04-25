#lang racket

(require "legacy-data.rkt")
(require "../../eopl.rkt")
(require (submod "../store.rkt" global-mutable))

(provide (all-defined-out))

(sllgen:define syntax-spec
  '(
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
    (Expression ("letrec" ProcDef (arbno ProcDef) "in" Expression) Letrec)
    (ProcDef
      (identifier "(" (separated-list identifier ",") ")"
        "=" Expression )
      MkProcDef)

    ; implicit references
    (Expression ("begin" (separated-list Expression ";") "end") Begin_)

    (Expression ("set" identifier "=" Expression) Set)
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
    (Var (var) (deref (apply-env env var)))
    (Diff (lhs rhs)
      (num-val (- (expval->num (eval lhs)) (expval->num (eval rhs))))
    )

    (Zero? (expr) (bool-val (zero? (expval->num (eval expr)))))

    (If (test texpr fexpr)
      (if (expval->bool (eval test)) (eval texpr) (eval fexpr))
    )

    (Let (vars vals body)
      (let ((new-env
        (extend-env* vars (map (compose newref eval) vals) env)))
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

    (Letrec (def defs expr) (eval-letrec (cons def defs) expr env))

    ; implicit reference
    (Begin_ (exprs) (last (map eval exprs)))

    (Set (ident expr)
      (setref! (apply-env env ident) (eval expr))
      (void-val)
    )

  ) ; cases
) ; value-of

(define (apply-procedure p args)
  (match p ((Procedure vars body env)
    (if (not (equal? (length args) (length vars)))
      (error 'apply-procedure
        "procedure arity mismatch between ~a (parameters) and ~a (arguments)"
        (length args) (length vars))
      (value-of body (extend-env* vars (map newref args) env))
    )
  ))
)

(define (eval-letrec recdefs expr env)
  (define (ProcDef->ProcInfo recdef)
    (cases ProcDef recdef
      (MkProcDef (var params body) (ProcInfo var params body))
    )
  )
  (define (make-rec-env recdefs env)
    (extend-env*-rec (map ProcDef->ProcInfo recdefs) env)
  )
  (let ((rec-env (make-rec-env recdefs env)))
    (value-of expr rec-env)
  )
)

((sllgen:make-rep-loop "sllgen> " value-of-program
   (sllgen:make-stream-parser eopl:lex-spec syntax-spec)))
