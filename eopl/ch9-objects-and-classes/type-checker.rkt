#lang racket

(require "../eopl.rkt")
(require "language.rkt")
(require "data.rkt")

(define (assert-type-equal! t texpected expr)
  (unless (equal? t texpected)
    (raise-user-error
      'TypeError "Expect ~v to have type ~v, but found ~v"
      expr texpected t)
  )
)
(define (assert-expr-type-in expr tp tenv)
  (assert-type-equal! (type-of expr tenv) tp expr)
)

; type-of : (Expression , environment) -> Type
(define (type-of expr tenv)
  (define (tp-of e) (type-of e tenv))

  (define (assert-expr-type expr tp)
    (assert-expr-type-in expr tp tenv)
  )

  (cases Expression expr
    (Num (n) (TInt))
    (Var (v) (apply-env tenv v))
    (Diff (lhs rhs)
      (assert-expr-type lhs (TInt))
      (assert-expr-type rhs (TInt))
      (TInt)
    )
    (Plus (lhs rhs)
      (assert-expr-type lhs (TInt))
      (assert-expr-type rhs (TInt))
      (TInt)
    )
    (Zero? (expr)
      (assert-expr-type expr (TInt))
      (TBool)
    )

    (If (test iftrue iffalse)
      (assert-expr-type test (TBool))
      (define t-tp (tp-of iftrue))
      (assert-expr-type iffalse t-tp)
      t-tp
    )
    
    (Let (vars vals body)
      (type-of body (extend-env* vars (map tp-of vals) tenv))
    )

    (Proc (params param-tps body) 
      (TFunc param-tps (type-of body (extend-env* params param-tps tenv)))
    )

    (Call (f args)
      (define f-tp (tp-of f))
      (cases Type f-tp
        (TFunc (params-tp ret-tp)
          (check-function-arity-error f (length params-tp) (length args))
          (map assert-expr-type args params-tp)
          ret-tp
        )
        (else (expect-some-type-error 'function f f-tp))
      )
    )

    (Letrec (defs body)
      (define let-body-env
        (extend-env*/binding (map letrecdef->binding defs) tenv))
      (map (λ (def) (check-letrecdef def let-body-env)) defs)
      (type-of body let-body-env)
    )

    (Nil (tp) (TList tp))

    (List (head tail)
      (define elem-tp (tp-of head))
      (map (λ (elem) (assert-expr-type elem elem-tp)) tail)
      (TList elem-tp)
    )

    (Set (var expr)
      (define var-tp (apply-env tenv var))
      (assert-expr-type expr var-tp)
      (TUnit)
    )

    (Begin_ (exprs) (last (map tp-of exprs)))
  )
)

(define (expect-some-type-error sometype expr t)
  (raise-user-error
    'TypeError "Expect ~v to have ~a type, but found ~v"
    expr sometype t)
)

(define (check-function-arity-error expr nparams nargs)
  (unless (equal? nparams nargs)
    (raise-user-error
      'TypeError "Function ~v has ~v parameters but provide ~v"
      expr nparams nargs)
  )
)

(define (letrecdef->binding def)
  (cases LetrecDef def
    (MkLetrecDef (ret-tp name params param-tps body)
      (cons name (TFunc param-tps ret-tp))
    )
  )
)

(define (check-letrecdef def env)
  (cases LetrecDef def
    (MkLetrecDef (ret-tp name params param-tps body)
      (define proc-body-env (extend-env* params param-tps env))
      (assert-expr-type-in body ret-tp proc-body-env)
    )
  )
)
