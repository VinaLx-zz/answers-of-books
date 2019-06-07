#lang racket

(provide (all-defined-out))

(require racket/undefined)

(require "../eopl.rkt")
(require (submod "../ch4-state/store.rkt" global-mutable))

(require "data.rkt")
(require "language.rkt")

(define (value-of expr env)
  (define (eval e) (value-of e env))
  (define (evals es) (map eval es))

  (cases Expression expr
    (Var (var) (deref (apply-env env var)))

    (Num (n) (num-val n))

    (Diff (lhs rhs)
      (num-val (- (expval->num (eval lhs)) (expval->num (eval rhs))))
    )

    (Plus (lhs rhs)
      (num-val (+ (expval->num (eval lhs)) (expval->num (eval rhs))))
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

    (Nil (tp) (list-val null))

    (List (head tail) (list-val (map eval (cons head tail))))

    (Begin_ (exprs) (last (map eval exprs)))

    (Set (ident expr)
      (define ref (apply-env env ident))
      (setref! ref (eval expr))
      (void-val)
    )

    ;; OOP

    (Self () (object-val (get-self-obj env)))

    (New (class-name e-args)
      (define cls (apply-class-env class-name))
      (define obj (new-object-of cls))
      (call-method (current-host-class env) obj constructor-name (evals e-args))
      (object-val obj)
    )

    (Super (method-name e-args)
      (call-super-method method-name (evals e-args) env)
    )

    (Send (e-obj method-name e-args)
      (define obj (expval->object (eval e-obj)))
      (call-method (current-host-class env) obj method-name (evals e-args))
    )

    ; ex 9.6.
    (InstanceOf (e-obj class-name)
      (define obj (expval->object (eval e-obj)))
      (bool-val (equal? (object-class-name obj) class-name))
    )

    ; ex 9.8.
    (FieldGet (e-obj field-name)
      (define obj (expval->object (eval e-obj)))
      (obj-field-get obj field-name)
    )
    (FieldSet (e-obj field-name expr)
      (define obj (expval->object (eval e-obj)))
      (obj-field-set obj field-name (eval expr))
      (void-val)
    )

    ; ex 9.9.
    (SuperFieldGet (field-name)
      (obj-field-get (get-super-obj env) field-name)
    )
    (SuperFieldSet (field-name expr)
      (obj-field-set (get-super-obj env) field-name (eval expr))
    )

    ; ex 9.10.
    (SendTo (class-name e-obj method-name e-args)
      (define obj (expval->object (eval e-obj)))
      (call-target-method
        (current-host-class env) obj class-name method-name (evals e-args))
    )

    (Cast (e-obj class-name) (eval e-obj))
  )
)

(define (extend-env*/let vars vals env)
  (extend-env* vars
    (map (λ (expr) (newref (value-of expr env))) vals)
    env)
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

; OO

(define (value-of-program program)
  (cases Program program (MkProgram (cls-decls expr)
    (initialize-class-env!)
    (initialize-store!)
    (map extend-class-env!/decl cls-decls)
    (value-of expr (empty-env))
  ))
)

(define (extend-class-env!/decl decl)
  (cases ClassDecl decl
    (CDeclClass
      (class-name super-class-name implements field-decls method-decls)

      (define super-class (apply-class-env super-class-name))
      (define fields (map FieldDecl->field field-decls))
      (define method-env
        (extend-method-env*/decl
          class-name method-decls (class_-method-env super-class)))
      (define cls
        (class_ class-name implements method-env fields super-class))
      (extend-class-env! class-name cls)
    )
    (CDeclInterface (interface-name methods) (void))
  )
)

(define (extend-method-env*/decl class-name method-decls env)
  (define (fold-step decl env) (extend-method-env/decl class-name decl env))
  (foldl fold-step env method-decls)
)

(define (extend-method-env/decl class-name decl env)
  (cases MethodDecl decl
    (MkMethodDecl (visibility sig body) (cases MethodSignature sig
    (MkMethodSignature (ret-t method-name params param-tps)
      (extend-env method-name (method visibility class-name params body) env)
    )))
  )
)

(define (get-self-obj env)
  (define obj (apply-env env self-var false))
  (if obj (expval->object obj) false)
)
(define (get-host-obj env)
  (define obj (apply-env env host-var false))
  (if obj (expval->object obj) false)
)
(define get-super-obj (compose object-super-obj get-host-obj))

; call-method : object -> symbol -> list expval -> result
(define (call-method host-class self method-name args)
  (define mthd (get-method self method-name))
  (apply-method host-class self mthd args)
)

(define (call-super-method method-name args env)
  (apply-method
    (current-host-class env)
    (get-self-obj env)
    (get-method (get-super-obj env) method-name) args)
)

(define/match (new-object-of cls)
  ((_) #:when (equal? cls object-class)
    (object cls (empty-env) false)
  )
  (((class_ _ _ _ field-names super-class))
    (define super-obj (new-object-of super-class))
    (define fields-env
      (extend-env*
        field-names (map (compose newref (const undefined)) field-names)
        (object-fields-env super-obj)))
    (object cls fields-env super-obj)
  )
)

(define (apply-method host-class self mthd args)
  (match-let*
    (((method visibility cls-name params body) mthd)
     (host-obj (target-super-object self cls-name))
     ((object _ fields-env _) host-obj))
    (guard-field-visibility visibility (apply-class-env cls-name) host-class)
    (define proc-env
      (extend-env host-var (object-val host-obj)
        (extend-env self-var (object-val self) fields-env)))
    (apply-procedure (Procedure params body proc-env) args)
  )
)

; ex 9.8.

(define (obj-field-get obj field-name)
  (deref (get-field-ref obj field-name))
)
(define (obj-field-set obj field-name val)
  (setref! (get-field-ref obj field-name) val)
)

; ex 9.10.
(define (call-target-method host-class self class-name method-name args)
  (define host-obj (target-super-object self class-name))
  (define mthd (get-method host-obj method-name))
  (apply-method host-class self mthd args)
)

; ex 9.11.
(define (guard-field-visibility callee-vis callee-cls caller-cls)
  (unless (visible? callee-vis callee-cls caller-cls)
    (error 'Visibility
      "cannot access field in class ~a with visibility ~v from ~a"
      (class_-name callee-cls) callee-vis
      (if caller-cls
        (format "class ~a" (class_-name caller-cls))
        "global environment"))
  )
)

(define (current-host-class env)
  (define host-obj (get-host-obj env))
  (if host-obj (object-class_ host-obj) false)
)

; ex 9.12.
(define (FieldDecl->field decl)
  (cases FieldDecl decl
    (MkFieldDecl (v tp name) name)
  )
)
