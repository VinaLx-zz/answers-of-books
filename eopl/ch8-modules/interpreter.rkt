#lang racket

(require "../eopl.rkt")
(require "data.rkt")
(require "language.rkt")
(provide (all-defined-out))

(define (value-of-program program)
  (cases Program program (MkProgram (mdefs expr)
    (expval->val (value-of expr (extend-env*/module mdefs (empty-env))))
  ))
)

(define (value-of expr env)
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

    (Let (vars vals body) (value-of body (extend-env*/let vars vals body)))

    (Proc (params types body) (make-procedure-val params body env))

    (Call (operator operands)
      (let ((proc (expval->proc (value-of operator env)))
            (args (map eval operands)))
        (apply-procedure proc args)
      )
    )
    (Letrec (defs body) (value-of body (extend-env*/letrec defs env)))

    ;; modules
    (QualifiedVar (mvar var) (look-up-qualified-var mvar var env))
  )
)

(define (apply-procedure p args)
  (match p ((Procedure vars body env)
    (if (not (equal? (length args) (length vars)))
      (error 'apply-procedure
        "procedure arity mismatch between ~a (formal args) and ~a (real args)"
        (length args) (length vars))
      (value-of body (extend-env* vars args env))
    )
  ))
)

(define (extend-env*/let vars vals env)
  (extend-env* vars (map (λ (expr) (value-of expr env))) env)
)

(define (extend-env*/letrec defs env)
  (define (LetrecDef->ProcInfo recdef)
    (cases LetrecDef recdef
      (MkLetrecDef (ret-t var params types body) (ProcInfo var params body))
    )
  )
  (extend-env*-rec (map LetrecDef->ProcInfo defs) env)
)

;; modules

(define (extend-env*/module module-defs env)
  (foldl extend-env/module env module-defs)
)
(define (extend-env/module module-def env)
  (cases ModuleDef module-def (MkModuleDef (name interf body)
    (define m (value-of-module-body body (exported-names interf) env))
    (extend-env name (module-val m) env)
  ))
)

; ex 8.2.
; adding only those names that are declared in the interface to the binding
(define (value-of-module-body module-body export-names env)
  (cases ModuleBody module-body (MkModuleBody (defs)
    (TypedModule (contruct-binding defs export-names env))
  ))
)

(define/match (contruct-binding defs names eval-env)
  (((quote ()) _ _) (empty-env))
  (((cons def defs1) (cons name names1) _)
    (cases MDefinition def (MkMDefinition (ident expr)
      (define val (value-of expr eval-env))
      (define eval-env1 (extend-env ident val eval-env))
      (if (equal? ident name)
        (extend-env name val (contruct-binding defs1 names1 eval-env1))
        (contruct-binding defs1 names eval-env1)
      )
    ))
  )
)

(define (exported-names interf)
  (define (decl->name decl)
    (cases MDeclaration decl (MkMDeclaration (name tp) name))
  )
  (cases ModuleInterface interf
    (MkModuleInterface (decls) (map decl->name decls))
  )
)
