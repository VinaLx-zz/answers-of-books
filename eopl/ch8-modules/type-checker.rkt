#lang racket

(provide (all-defined-out))

(require "data.rkt")
(require "language.rkt")
(require "../eopl.rkt")

(define (assert-subtype! sub-t super-t tenv expr)
  (unless (<: sub-t super-t tenv)
    (raise-user-error
      'TypeError "Expect ~v to have type ~v, but found ~v"
      expr super-t sub-t)
  )
)
(define (assert-expr-type-in expr tp tenv)
  (assert-subtype! (type-of expr tenv) tp tenv expr)
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
      (check-call f args tenv tp-of)
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

(define (check-call f args tenv tp-of)
  (define f-tp (tp-of f))
  (define (assert-expr-type expr tp)
    (assert-subtype! (tp-of expr) tp tenv expr)
  )
  (cases Type f-tp
    (TFunc (param-ts ret-t)
      (check-function-arity-error f (length param-ts) (length args))
      (define arg-ts (map tp-of args))
      (check-call-impl param-ts arg-ts ret-t tenv args)
    )
    (else (expect-some-type-error 'function f f-tp))
  )
)
(define (check-call-impl param-ts args-ts ret-t tenv args)
  (match* (param-ts args-ts args)
    (((quote ()) (quote ()) (quote ())) ret-t)
    (((cons param-t param-ts) (cons arg-t arg-ts) (cons arg args))
      (assert-subtype! arg-t param-t tenv arg)
      (match-define (cons (cons ret-t1 param-ts1) tenv1)
        (rewrite-dependents param-t arg-t tenv (cons ret-t param-ts)))
      (check-call-impl param-ts1 arg-ts ret-t1 tenv1 args)
    )
  )
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
  (cases ModuleDef module-def
    (ModDefModule (name interf body)
      (printf "----- checking module ~v -----\n" name)
      (check-duplicate-module name tenv)
      (define body-tp (type-of-module-body body tenv))
      (printf "[DEBUG] type of body\n" )
      (pretty-print body-tp)
      (define inte-tp (interface->type name interf tenv))
      (printf "[DEBUG] type of interface\n" )
      (pretty-print inte-tp)
      (assert-subtype! body-tp inte-tp tenv body)
      (printf "[DEBUG] pass subtype check\n")
      (define inte-tp2 (expand-top-decls inte-tp tenv))
      (printf "[DEBUG] type of final interface\n")
      (pretty-print inte-tp2)
      (extend-env name inte-tp2 tenv)
    )
    (ModDefInterface (ivar interf)
      (extend-tenv/alias ivar (interface->type false interf tenv) tenv)
    )
  )
)

(define (type-of-module-body module-body tenv)
  (cases ModuleBody module-body
    (MBDefinitions (defs)
      (TModule (MNNone) (defs->decls defs tenv))
    )
    (MBLet (vars vals body)
      (define body-env (check-letrecdefs vars vals tenv))
      (type-of-module-body body body-env)
    )
    (MBLetrec (letrec-defs body)
      (define body-env (check-letrecdefs letrec-defs tenv))
      (type-of-module-body body body-env)
    )
    (MBModule (module-def body)
      (define body-env (extend-tenv/module module-def tenv))
      (type-of-module-body body body-env)
    )
    (MBVar (mvar)
      (apply-tenv tenv mvar)
    )
    (MBProc (params interfs body)
      (define body-env (extend-tenv/module-proc-params params interfs tenv))
      (TFunc
        (map
          (λ (param interf) (interface->type param interf tenv)) params interfs)
        (type-of-module-body body body-env))
    )
    (MBCall (mproc margs)
      (define (tp-of-body m) (type-of-module-body m tenv))
      (check-call mproc margs tenv tp-of-body)
    )
  )
)

(define (interface->type name interf tenv)
  (define oname (if name (MNJust name) (MNNone)))
  (define (interface->tp name interf) (interface->type name interf tenv))
  (cases ModuleInterface interf
    (MIDecls (decls) (TModule oname decls))
    (MIProc (params interfs ret-interf)
      (TFunc (map interface->tp params interfs)
             (interface->tp false ret-interf))
    )
    (MIVar (ivar)
      (define tp (apply-tenv/alias tenv ivar))
      (set-unexpanded-module-name tp name)
    )
  )
)
(define (type-of-module-interface name interf tenv)
  (define (interface->tp name interf) (interface->type name interf tenv))
  (cases ModuleInterface interf
    (MIDecls (decls)
      (TModule (MNJust name) (expand-decls name decls tenv))
    )
    (MIProc (params interfs ret-interf)
      (TFunc (map interface->tp params interfs)
             (interface->tp false ret-interf))
    )
    (MIVar (ivar)
      (define tp (apply-tenv/alias tenv ivar))
      (expand-module-type name tp tenv)
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

(define/match (<:-decls sub-decls super-decls tenv)
  ((_ (quote ()) _) true)
  (((quote ()) _ _) false)
  (((cons d1 ds1) (cons d2 ds2) _)
    (if (equal? (decl->name d1) (decl->name d2))
      (and (<:-decl d1 d2 tenv)
        (<:-decls ds1 ds2 (extend-tenv/decl d1 tenv)))
      (<:-decls ds1 super-decls tenv)
    )
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
      (TModule (oname decls)
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
    (TModule (oname decls) (expand-decls (get-name oname) decls tenv))
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

(define (decl->name decl)
  (cases MDeclaration decl
    (MDecVar (var tp) var)
    (MDecTrans (var tp) var)
    (MDecOpaque (var) var)
  )
)

(define (<:-decl d1 d2 tenv)
  (printf "[DEBUG] decl-<: ~v\n                ~v\n" d1 d2)
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

(define (expand-decls mvar decls tenv)
  (match decls
    ((quote ()) null)
    ((cons decl decls1)
      (define-values (e-decl tenv1) (expand-type-decl mvar decl tenv))
      (cons e-decl (expand-decls mvar decls1 tenv1))
    )
  )
)


(define (extend-tenv/decl decl tenv)
  (printf "[DEBUG] extend-tenv/decl ~v\n" decl)
  (cases MDeclaration decl
    (MDecVar (var tp) tenv
      ; (extend-env var (expand-type tp tenv) tenv)
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

;; module procedure

(define (new-module-name) (gensym 'module))
(define (get-name opt)
  (cases OptionalModuleName opt
    (MNJust (name) name)
    (MNNone () (new-module-name))
  )
)

(define (<: t1 t2 tenv)
  (printf "[DEBUG] <: ~v\n           ~v\n" t1 t2)
  (cases Type t1
    (TModule (oname decls1) (cases Type t2
      (TModule (oname decls2) (<:-decls decls1 decls2 tenv))
      (else false)
    ))
    (TFunc (param-ts1 ret-t1) (cases Type t2
      (TFunc (param-ts2 ret-t2)
        (<:-func param-ts1 param-ts2 ret-t1 ret-t2 tenv)
      )
      (else false)
    ))
    (else (equal? (expand-type t1 tenv) (expand-type t2 tenv)))
  )
)

(define (<:-func param-ts1 param-ts2 ret-t1 ret-t2 tenv)
  (match* (param-ts1 param-ts2)
    (((quote ()) (quote ())) (<: ret-t1 ret-t2 tenv))
    (((cons param-t1 param-ts1) (cons param-t2 param-ts2))
      (if (<: param-t2 param-t1 tenv)
        (match-let
          (((cons (cons ret-t1/ param-ts1/) tenv/)
            (rewrite-dependents
              param-t1 param-t2 tenv (cons ret-t1 param-ts1))))
          (<:-func param-ts1/ param-ts2 ret-t1/ ret-t2 tenv/)
        )
        false
      )
    )
  )
)

(define (rename-module tp from to)
  (define (recurse t) (rename-module t from to))
  (cases Type tp
    (TQualified (mvar var)
      (if (equal? from mvar) (TQualified to var) tp )
    )
    (TFunc (param-ts ret-ts)
      (TFunc (map recurse param-ts) (recurse ret-ts))
    )
    (TModule (oname decls)
      (if (equal? (get-name oname) from) tp
        (TModule oname (map (λ (decl) (rename-module/decl decl from to)) decls))
      )
    )
    (else tp)
  )
)
(define (rename-module/decl decl from to)
  (cases MDeclaration decl
    (MDecVar (var tp) (MDecVar var (rename-module tp from to)))
    (MDecTrans (var tp) (MDecTrans var (rename-module tp from to)))
    (MDecOpaque (var) decl)
  )
)

(define (rewrite-dependents origin-t new-t tenv ret-ts)
  (cases Type origin-t
    (TModule (oname-o decls-o) (cases Type new-t
      (TModule (oname-n decls-n)
        (define old-name (get-name oname-o))
        (define new-name (get-name oname-n))
        (define (rename t) (rename-module t old-name new-name))
        (define new-ret-ts (map rename ret-ts))
        (define new-tenv
           (extend-env new-name
             (TModule (MNJust new-name) (expand-decls new-name decls-o tenv))
             tenv))
        (cons new-ret-ts new-tenv)
      )
      (else (cons ret-ts tenv))
    ))
    (else (cons ret-ts tenv))
  )
)

; ex 8.25.

(define/match (extend-tenv/module-proc-params params interfs tenv)
  (((quote ()) (quote ()) _) tenv)
  (((cons param params/) (cons interf interfs/) _)
    (extend-tenv/module-proc-params params/ interfs/
      (extend-env param (type-of-module-interface param interf tenv) tenv))
  )
)

; ex 8.27.
(define (expand-top-decls tp tenv)
  (cases Type tp
    (TModule (oname decls)
      (define name (get-name oname))
      (TModule (MNJust name) (expand-decls name decls tenv))
    )
    (else tp)
  )
)
(define (set-unexpanded-module-name tp name)
  (cases Type tp
    (TModule (oname decls) (TModule (MNJust name) decls))
    (else tp)
  )
)
(define (expand-module-type name tp tenv)
  (cases Type tp
    (TModule (oname decls)
      (TModule (MNJust name) (expand-decls name decls tenv))
    )
    (else tp)
  )
)
