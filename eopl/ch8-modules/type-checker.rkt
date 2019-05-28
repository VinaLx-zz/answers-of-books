#lang racket

(provide (all-defined-out))

(require "data.rkt")
(require "language.rkt")
(require "../eopl.rkt")

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

(define (apply-tenv env var)
  (match (apply-env env var false)
    (#f (raise-user-error
      'TypeError "binding of ~a is not found in environment ~v"
      var env)
    )
    (t t)
  )
)

(define (type-of expr tenv)
  (define (tp-of e) (type-of e tenv))

  (define (assert-expr-type expr tp)
    (assert-expr-type-in expr tp tenv)
  )

  (cases Expression expr
    (Num (n) (TInt))
    (Var (v) (apply-tenv tenv v))
    (Diff (lhs rhs)
      (assert-expr-type lhs (TInt))
      (assert-expr-type rhs (TInt))
      (TInt)
    )
    (Zero? (expr)
      (assert-expr-type expr (TInt))
      (TBool)
    )
    (Let (vars vals body)
      (type-of body (check-letdefs vars vals tenv))
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
      (define let-body-env (check-letrecdefs defs tenv))
      (type-of body let-body-env)
    )
    (If (test iftrue iffalse)
      (assert-expr-type test (TBool))
      (define t-tp (tp-of iftrue))
      (assert-expr-type iffalse t-tp)
      t-tp
    )

    ;; modules
    (QualifiedVar (mvar var vars)
      (define module-type (apply-tenv tenv mvar))
      (type-of-qualified-var module-type (cons var vars) mvar expr)
    )
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

(define (check-letdefs vars vals env)
  (extend-env* vars (map (λ (val) (type-of val env)) vals) env)
)

(define (check-letrecdefs defs env)
  (define let-body-env (extend-tenv*/letrec defs env))
  (map (λ (def) (check-letrecdef def let-body-env)) defs)
  let-body-env
)

(define (extend-tenv*/letrec defs env)
  (define (letrecdef->binding def)
    (cases LetrecDef def
      (MkLetrecDef (ret-tp name params param-tps body)
        (cons name (TFunc param-tps ret-tp))
      )
    )
  )
  (extend-env*/binding (map letrecdef->binding defs) env)
)

(define (check-letrecdef def env)
  (cases LetrecDef def
    (MkLetrecDef (ret-tp name params param-tps body)
      (define proc-body-env (extend-env* params param-tps env))
      (assert-expr-type-in body ret-tp proc-body-env)
    )
  )
)

;; module

(define (type-of-program program)
  (cases Program program
    (MkProgram (module-defs expr)
      (define main-tenv (extend-tenv*/module module-defs (empty-env)))
      (type-of expr main-tenv)
    )
  )
)

(define (binding-not-found-in-module var tmodule expr)
  (raise-user-error
    'TypeError "Expect module type ~v to have binding of ~a in expression ~v"
    tmodule var expr)
)

(define (assoc-decls var decls)
  (match decls
    ((quote ()) #f)
    ((cons decl decls1)
      (cases MDeclaration decl (MkMDeclaration (ident t)
        (if (equal? var ident) t (assoc-decls var decls1))
      ))
    )
  ) ; match
)

(define (extend-tenv*/module module-defs tenv)
  (foldl extend-tenv/module tenv module-defs)
)

(define (extend-tenv/module module-def tenv)
  (cases ModuleDef module-def (MkModuleDef (name interf body)
    (check-duplicate-module name tenv)
    (cases ModuleInterface interf (MkModuleInterface (decls)
      (check-module-body-match-decls body decls tenv name)
      (extend-env name (TModule decls) tenv)
    ))
  ))
)

(define (check-module-body-match-decls body decls tenv name)
  (define full-decls (module-full-decls body tenv))
  (unless (decls-<:? full-decls decls)
    (raise-user-error
      'TypeError "Definitions of module ~a: ~v don't match the interfaces: ~v"
      name full-decls decls)
  )
)

(define (module-full-decls module-body tenv)
  (cases ModuleBody module-body
    (MBDefinitions (defs)
      (defs-full-decls defs tenv)
    )
    (MBLet (vars vals body)
      (module-full-decls body (check-letdefs vars vals tenv))
    )
    (MBLetrec (letrec-defs body)
      (module-full-decls body (check-letrecdefs letrec-defs tenv))
    )
    (MBModule (module-def body)
      (module-full-decls body (extend-tenv/module module-def tenv))
    )
  )
)

(define/match (defs-full-decls defs tenv)
  (((quote ()) _) null)
  (((cons def defs1) _)
    (cases MDefinition def (MkMDefinition (var expr)
      (define tp (type-of expr tenv))
      (cons
        (MkMDeclaration var tp)
        (defs-full-decls defs1 (extend-env var tp tenv)))
    ))
  )
)

(define/match (decls-<:? sub-decls super-decls)
  ((_ (quote ())) true)
  (((quote ()) _) false)
  (((cons d1 ds1) (cons d2 ds2))
    (cases MDeclaration d1 (MkMDeclaration (var1 tp1)
    (cases MDeclaration d2 (MkMDeclaration (var2 tp2)
      (if (equal? var1 var2)
        (and (<: tp1 tp2) (decls-<:? ds1 ds2))
        (decls-<:? ds1 (cons d2 ds2))
      )
    ))))
  )
)

(define (<: t1 t2)
  (cases Type t1
    (TModule (decls1)
      (cases Type t2
        (TModule (decls2) (decls-<:? decls1 decls2))
        (else false)
      )
    )
    (else (equal? t1 t2))
  )
)

; ex 8.1 rejecting program that defines two modules with the same name.
(define (check-duplicate-module new-name tenv)
  (when (apply-env tenv new-name false)
    (raise-user-error
      'TypeError "Duplicate module declaration: ~a" new-name)
  )
)

; ex 8.7. nested module
(define/match (type-of-qualified-var mtype vars mvar expr)
  ((_ (quote ()) _ _) mtype)
  ((_ (cons var vars1) _ _)
    (cases Type mtype
      (TModule (decls)
        (match (assoc-decls var decls)
          (#f (binding-not-found-in-module var mtype expr))
          (tp (type-of-qualified-var tp vars1 var expr))
        )
      )
      (else (expect-some-type-error 'module mvar mtype))
    )
  )
)
