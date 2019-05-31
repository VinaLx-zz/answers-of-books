#lang racket

(require "data.rkt")
(require "language.rkt")
(require "../eopl.rkt")
(require (submod "../ch4-state/store.rkt" global-mutable))

(define (value-of expr env)
  (define (eval e) (value-of e env))

  (cases Expression expr
    (Var (var) (deref (apply-env env var)))

    (Num (n) (num-val n))

    (Diff (lhs rhs)
      (num-val (- (expval->num (eval lhs)) (expval->num (eval rhs))))
    )

    (Zero? (expr) (bool-val (zero? (expval->num (eval expr)))))

    (If (test texpr fexpr)
      (if (expval->bool (eval test)) (eval texpr) (eval fexpr))
    )

    (Let (vars vals body)
      (value-of body (extend-env*/let vars vals env))
    )

    (Proc (params tps body) (make-procedure-val params body env))

    (Call (operator operands)
      (apply-procedure (expval->proc (eval operator)) (map eval operands))
    )

    (Letrec (defs body) (value-of body (extend-env*/letrec defs env)))

    (Begin_ (exprs) (last (map eval exprs)))

    (Set (ident expr)
      (define ref (apply-env env ident))
      (setref! ref (eval expr))
      (void-val)
    )
  )
)

(define (extend-env*/let vars vals env)
  (extend-env* vars (map (λ (expr) (value-of expr env)) vals) env)
)

(define (apply-procedure p args)
  (match p ((Procedure params body env)
    (define-values (nparam narg) (values (length params) (length args)))
    (unless (equal? nparam narg)
      (error 'apply-procedure
        "procedure arity mismatch between ~a (args) and ~a (params)"
        narg nparam)
    )
    (value-of body (extend-env* params (map newref args) env))
  ))
)

(define (extend-env*/letrec defs env)
  (define (LetrecDef->ProcInfo recdef)
    (cases LetrecDef recdef
      (MkLetrecDef (ret-t var params types body) (ProcInfo var params body))
    )
  )
  (extend-env*-rec (map LetrecDef->ProcInfo defs) env)
)
