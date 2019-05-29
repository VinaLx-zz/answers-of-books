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
      'TypeError "binding of variable ~a is not found in environment ~v"
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
      (TFunc param-tps (type-of body (extend-tenv* params param-tps tenv)))
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
      (apply-tenv*/qualified tenv mvar (cons var vars) expr)
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
  (extend-tenv* vars (map (λ (val) (type-of val env)) vals) env)
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
  (extend-tenv*/binding (map letrecdef->binding defs) env)
)

(define (check-letrecdef def env)
  (cases LetrecDef def
    (MkLetrecDef (ret-tp name params param-tps body)
      (define proc-body-env (extend-tenv* params param-tps env))
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

(define (assoc-decl var decl)
  (cases MDeclaration decl
    (MDecVar (ident tp) (and (equal? ident var) tp))
    (MDecTrans (tvar tp) (and (equal? (type-var tvar) var) tp))
    (MDecOpaque (tvar) (TQualified '__UNKNOWN__ tvar))
  )
)
(define/match (assoc-decls var decls)
  ((_ (quote ())) #f)
  ((_ (cons decl decls1))
    (or (assoc-decl var decl) (assoc-decls var decls1))
  )
)

(define (extend-tenv*/module module-defs tenv)
  (foldl extend-tenv/module tenv module-defs)
)

(define (extend-tenv/module module-def tenv)
  (cases ModuleDef module-def (MkModuleDef (name interf body)
    (check-duplicate-module name tenv)
    (cases ModuleInterface interf (MkModuleInterface (decls)
      (check-module-body-match-decls body decls tenv name)
      (extend-env name (TModule (expand-type-decls name decls tenv)) tenv)
    ))
  ))
)

(define (check-module-body-match-decls body decls tenv name)
  (define full-decls (module-full-decls body tenv))
  (unless (decls-<:? full-decls decls tenv)
    (raise-user-error
      'TypeError "Definitions of module ~a: ~v don't match the interfaces: ~v"
      name full-decls decls)
  )
)

(define (module-full-decls module-body tenv)
  (cases ModuleBody module-body
    (MBDefinitions (defs)
      (defs->decls defs tenv)
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

(define (def->decl def tenv)
  (cases MDefinition def
    (MDefVar (var expr)
      (define tp (type-of expr tenv))
      (values (MDecVar var tp) (extend-tenv var tp tenv))
    )
    (MDefType (tvar tp)
      (define tp1 (expand-type tp tenv))
      (values (MDecTrans tvar tp1) (extend-tenv/alias tvar tp1 tenv))
    )
  )
)
(define/match (defs->decls defs tenv)
  (((quote ()) _) null)
  (((cons def defs1) _)
    (define-values (decl tenv1) (def->decl def tenv))
    (cons decl (defs->decls defs1 tenv1))
  )
)

(define/match (decls-<:? sub-decls super-decls tenv)
  ((_ (quote ()) _) true)
  (((quote ()) _ _) false)
  (((cons d1 ds1) (cons d2 ds2) _)
    (if (equal? (decl->name d1) (decl->name d2))
      (and (decl-<:? d1 d2 tenv)
        (decls-<:? ds1 ds2 (extend-tenv/decl d1 tenv)))
      (decls-<:? ds1 super-decls tenv)
    )
  )
)

(define (<: t1 t2 tenv)
  (cases Type t1
    (TModule (decls1)
      (cases Type t2
        (TModule (decls2) (decls-<:? decls1 decls2 tenv))
        (else false)
      )
    )
    (else (equal? (expand-type t1 tenv) (expand-type t2 tenv)))
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
(define (apply-tenv/qualified tenv mvar var expr)
  (apply-tenv*/qualified tenv mvar (list var) expr)
)
(define (apply-tenv*/qualified tenv mvar vars expr)
  (type-of-qualified-var (apply-tenv tenv mvar) vars mvar expr)
)
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

;; opaque types

(define (extend-tenv/alias var tp tenv)
  (extend-env (type-var var) tp tenv)
)
(define (apply-tenv/alias tenv var)
  (apply-tenv tenv (type-var var))
)

(define (expand-type tp tenv)
  (define (recurse t) (expand-type t tenv))
  (cases Type tp
    (TInt () (TInt))
    (TBool () (TBool))
    (TFunc (arg-ts ret-t) (TFunc (map recurse arg-ts) (recurse ret-t)))
    (TAlias (tvar) (apply-tenv/alias tenv tvar))
    (TQualified (mvar tvar)
      (apply-tenv/qualified tenv mvar (type-var tvar) tp)
    )
    ; TODO: binding the module name to '__UNKNOWN__ is wrong
    (TModule (decls) (expand-type-decls '__UNKNOWN__ decls tenv))
  )
)

(define (expand-type-decl mvar decl tenv)
  (cases MDeclaration decl
    (MDecVar (var tp)
      (values (MDecVar var (expand-type tp tenv)) tenv)
    )
    (MDecTrans (var tp)
      (define expanded-t (expand-type tp tenv))
      (define tenv1 (extend-tenv/alias var expanded-t tenv))
      (values (MDecTrans var expanded-t) tenv1)
    )
    (MDecOpaque (tvar)
      (define expanded-t (TQualified mvar tvar))
      (define tenv1 (extend-tenv/alias tvar expanded-t tenv))
      (values (MDecTrans tvar expanded-t) tenv1)
    )
  )
)
(define (expand-type-decls mvar decls tenv)
  (match decls
    ((quote ()) null)
    ((cons decl decls1)
      (define-values (e-decl tenv1) (expand-type-decl mvar decl tenv))
      (cons e-decl (expand-type-decls mvar decls1 tenv1))
    )
  )
)

(define (decl->name decl)
  (cases MDeclaration decl
    (MDecVar (var tp) var)
    (MDecTrans (var tp) var)
    (MDecOpaque (var) var)
  )
)

(define (decl-<:? d1 d2 tenv)
  (cases MDeclaration d1
    (MDecVar (var1 t1)
      (cases MDeclaration d2
        (MDecVar (var2 t2) (and (equal? var1 var2) (<: t1 t2 tenv)))
        (else false)
      )
    )
    (MDecTrans (var1 t1)
      (cases MDeclaration d2
        (MDecTrans (var2 t2) (and (equal? var1 var2) (<: t1 t2 tenv)))
        (MDecOpaque (var2) (equal? var1 var2))
        (else false)
      )
    )
    (MDecOpaque (var1)
      (cases MDeclaration d2
        (MDecOpaque (var2) (equal? var1 var2))
        (else false)
      )
    )
  )
)

(define (extend-tenv/decl decl tenv)
  (cases MDeclaration decl
    (MDecVar (var tp)
      (extend-env var (expand-type tp tenv) tenv)
    )
    (MDecTrans (tvar tp)
      (extend-tenv/alias tvar (expand-type tp tenv) tenv)
    )
    (MDecOpaque (tvar)
      (extend-tenv/alias tvar (TQualified '__UNKNOWN__ tvar) tenv)
    )
  )
)

; ex 8.18.
; Robustly maintain the invariant by inserting the expansion in
; `extend-tenv`

(define (extend-tenv var tp tenv)
  (extend-env var (expand-type tp tenv) tenv)
)
(define (extend-tenv/binding b env)
  (extend-tenv (car b) (cdr b) env)
)
(define (extend-tenv*/binding bs env)
  (foldl extend-tenv/binding env bs)
)
(define (extend-tenv* vars tps tenv)
  (extend-tenv*/binding (zip vars tps) tenv)
)

