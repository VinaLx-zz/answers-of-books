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

    (Let (vars vals body) (value-of body (extend-env*/let vars vals env)))

    (Proc (params types body) (make-procedure-val params body env))

    (Call (operator operands)
      (define proc (expval->proc (eval operator)))
      (define args (map eval operands))
      (apply-procedure proc args)
    )

    (Letrec (defs body) (value-of body (extend-env*/letrec defs env)))

    ;; modules
    (QualifiedVar (mvar var vars)
      (eval-qualified-var (apply-env env mvar) (cons var vars))
    )
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
  (extend-env* vars (map (λ (expr) (value-of expr env)) vals) env)
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
    (extend-env name m env)
  ))
)

; ex 8.2.
; adding only those names that are declared in the interface to the binding
(define (value-of-module-body module-body export-names env)
  (cases ModuleBody module-body
    (MBDefinitions (defs)
      (module-val (TypedModule (contruct-binding defs export-names env)))
    )
    (MBLet (vars vals body)
      (define let-body-env (extend-env*/let vars vals env))
      (value-of-module-body body export-names let-body-env)
    )
    (MBLetrec (letrec-defs body)
      (define let-body-env (extend-env*/letrec letrec-defs env))
      (value-of-module-body body export-names let-body-env)
    )
    (MBModule (module-def body)
      (define body-env (extend-env/module module-def env))
      (value-of-module-body body export-names body-env)
    )
    (MBVar (mvar)
      (apply-env env mvar)
    )
    (MBProc (param tp body)
      (module-proc-val (Procedure (list param) body env))
    )
    (MBCall (mvar argvar)
      (define mp (expval->module-proc (apply-env env mvar)))
      (apply-module-procedure mp (list (apply-env env argvar)) export-names)
    )
  )
)

(define/match (contruct-binding defs names eval-env)
  (((quote ()) _ _) (empty-env))
  (((cons def defs1) (cons name names1) _)
    (cases MDefinition def
      (MDefVar (ident expr)
        (define val (value-of expr eval-env))
        (define eval-env1 (extend-env ident val eval-env))
        (if (equal? ident name)
          (extend-env name val (contruct-binding defs1 names1 eval-env1))
          (contruct-binding defs1 names eval-env1)
        )
      )
      (else (contruct-binding defs1 names eval-env))
    )
  )
)

(define (exported-names interf)
  (define/match (exported-names-decls decls)
    (((quote ())) null)
    (((cons decl decls1))
      (cases MDeclaration decl
        (MDecVar (name tp) (cons name (exported-names-decls decls1)))
        (else (exported-names-decls decls1))
      )
    )
  )
  (cases ModuleInterface interf
    (MIDecls (decls) (exported-names-decls decls))
    (MIProc (param tp body) null)
  )
)

; ex 8.7. nested module
(define/match (eval-qualified-var mval vars)
  ((_ (quote ())) mval)
  ((_ (cons var vars1))
    (match (expval->module mval) ((TypedModule binding)
      (eval-qualified-var (apply-env binding var) vars1)
    ))
  )
)

;; module procedure

(define (apply-module-procedure p args export-names)
  (match p ((Procedure params body env)
    (define-values (nparam narg) (values (length params) (length args)))
    (unless (equal? nparam narg)
      (error 'apply-module-procedure
        "procedure arity mismatch between ~a (args) and ~a (params)"
        narg nparam)
    )
    (value-of-module-body body export-names (extend-env* params args env))
  ))
)
