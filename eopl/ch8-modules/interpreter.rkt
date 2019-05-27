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

    (Let (vars vals body)
      (let ((new-env
        (extend-env* vars (map eval vals) env)))
        (value-of body new-env)
      )
    )

    (Proc (params types body) (make-procedure-val params body env))

    (Call (operator operands)
      (let ((proc (expval->proc (value-of operator env)))
            (args (map eval operands)))
        (apply-procedure proc args)
      )
    )
    (Letrec (defs body) (eval-letrec defs body env))

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

(define (eval-letrec recdefs expr env)
  (define (LetrecDef->ProcInfo recdef)
    (cases LetrecDef recdef
      (MkLetrecDef (ret-t var params types body) (ProcInfo var params body))
    )
  )
  (define (make-rec-env recdefs env)
    (extend-env*-rec (map LetrecDef->ProcInfo recdefs) env)
  )
  (let ((rec-env (make-rec-env recdefs env)))
    (value-of expr rec-env)
  )
)

;; modules

(define (extend-env*/module module-defs env)
  (foldl extend-env/module env module-defs)
)
(define (extend-env/module module-def env)
  (cases ModuleDef module-def (MkModuleDef (name interfaces body)
    (extend-env name (module-val (value-of-module-body body env)) env)
  ))
)

(define (value-of-module-body module-body env)
  (define (make-env-from-defs defs eval-env)
    (match defs
      ((quote ()) (empty-env))
      ((cons def defs1) (cases MDefinition def (MkMDefinition (ident expr)
        (define val (value-of expr eval-env))
        (extend-env ident val
          (make-env-from-defs defs1 (extend-env ident val eval-env)))
      )))
    )
  )
  (cases ModuleBody module-body (MkModuleBody (defs)
    (TypedModule (make-env-from-defs defs env))
  ))
)

