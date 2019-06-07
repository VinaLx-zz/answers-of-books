#lang racket

(provide (all-defined-out))

(require "../eopl.rkt")
(require "language.rkt")
(require "data.rkt")

(define (assert-subtype! t texpected expr)
  (unless (t . <: . texpected)
    (raise-user-error
      'TypeError "Expect ~v to have type ~v, but found ~v"
      expr texpected t)
  )
)
(define (assert-expr-type-in expr tp tenv)
  (assert-subtype! (type-of expr tenv) tp expr)
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

    (Call (f args) (check-call (tp-of f) args tenv f))

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

    (Self () (apply-env tenv self-var))

    (New (class-name args)
      (define cls (apply-class-tenv/class class-name))
      (define mthd (check-class-method cls constructor-name expr))
      (check-method-call mthd args tenv)
      (TClass class-name)
    )

    (Send (e-obj method-name args)
      (define t-obj (check-class-like (tp-of e-obj) e-obj))
      (define mthd (check-class-method t-obj method-name expr))
      (check-method-call mthd args tenv)
    )

    (Super (method-name args)
      (define host-class (check-host-class tenv expr))
      (define super-class (check-super-class host-class expr))
      (define mthd (check-class-method super-class method-name expr))
      (check-method-call mthd args tenv)
    )

    (InstanceOf (e-obj class-name)
      (define cls1 (check-class-like (tp-of e-obj) expr))
      (define cls2 (check-apply-class-env class-name))
      (check-related-types cls1 cls2 expr)
      (TBool)
    )

    (Cast (e-obj class-name)
      (define cls1 (check-class-like (tp-of e-obj) e-obj))
      (define cls2 (check-apply-class-env class-name))
      (check-related-types cls1 cls2 expr)
      (TClass class-name)
    )

    (FieldGet (e-obj field-name)
      (define cls (check-class (tp-of e-obj) e-obj))
      (define field (check-class-field cls field-name expr))
      (static-field-type field)
    )
    (FieldSet (e-obj field-name val)
      (define cls (check-class (tp-of e-obj) e-obj))
      (define field (check-class-field cls field-name expr))
      (assert-expr-type val (static-field-type field))
      (TUnit)
    )

    (SuperFieldGet (field-name)
      (define host-class (check-host-class tenv expr))
      (define super-class (check-target-super-class host-class expr))
      (define field (check-class-field super-class field-name expr))
      (static-field-type field)
    )

    (SuperFieldSet (field-name val)
      (define host-class (check-host-class tenv expr))
      (define super-class (check-target-super-class host-class expr))
      (define field (check-class-field super-class field-name expr))
      (assert-expr-type val (static-field-type field))
      (TUnit)
    )

    (SendTo (class-name e-obj method-name args)
      (define cls (check-class (tp-of e-obj) e-obj))
      (define host-cls (check-target-super-class cls class-name expr))
      (define mthd (check-class-method host-cls method-name expr))
      (check-method-call mthd args tenv)
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

(define (check-call f-tp args tenv f)
  (define (assert-expr-type expr tp)
    (assert-subtype! (type-of expr tenv) tp expr)
  )
  (cases Type f-tp
    (TFunc (param-ts ret-t)
      (check-function-arity-error f (length param-ts) (length args))
      (map assert-expr-type args param-ts)
      ret-t
    )
    (else (expect-some-type-error 'function f f-tp))
  )
)

;; typed OO

(define (extend-class-tenv*!/decls class-decls)
  (map extend-class-tenv!/decl class-decls)
)

(define (extend-class-tenv!/decl class-decl)
  (cases ClassDecl class-decl
    (CDeclClass (name super-name ifs field-decls method-decls)
      (define super-class (apply-class-tenv/class super-name))
      (define interfaces (map apply-class-tenv/interface ifs))
      (define field-env
        (extend-field-env* field-decls (class_-fields super-class)))
      (define method-env
        (extend-method-env* method-decls (class_-method-env super-class)))
      (check-implement-all-interfaces method-env interfaces name)
      (extend-class-env! name
        (class_ name interfaces method-env field-env super-class))
      (check-method-definitions name method-decls (field-env->tenv field-env))
    )
    (CDeclInterface (name abs-method-decls)
      (extend-class-env!
        name (interface_
          name (extend-tenv*/AbsMethodDecl abs-method-decls (empty-env))))
    )
  )
)

; class initialization

(define (extend-field-env* field-decls tenv)
  (foldl extend-field-env tenv field-decls)
)
(define (extend-field-env field-decl tenv)
  (define field (FieldDecl->static-field field-decl))
  (extend-env (static-field-name field) field tenv)
)
(define (FieldDecl->static-field field-decl)
  (cases FieldDecl field-decl
    (MkFieldDecl (v tp name) (static-field name tp v))
  )
)

(define (extend-method-env* method-decls method-env)
  (foldl extend-method-env method-env method-decls)
)

(define (extend-method-env method-decl method-env)
  (define mthd (MethodDecl->static-method method-decl))
  (extend-env (static-field-name mthd) mthd method-env)
)

(define (MethodDecl->static-method method-decl)
  (cases MethodDecl method-decl (MkMethodDecl (v signature body)
    (cases MethodSignature signature
      (MkMethodSignature (ret-t name params param-ts)
        (static-method name (TFunc param-ts ret-t) v)
      )
    )
  ))
)

(define (check-implement-all-interfaces method-env interfaces class-name)
  (define (check-implement-interface intf)
    (define/match (check-implement-method mthd)
      (((static-method name type public_))
        (define mthd-impl (apply-env method-env name false))
        (unless (equal? mthd-impl mthd)
          (raise-user-error 'Class
            "method ~a of interface ~a is not implemented by class ~a"
            name (interface_-name intf) class-name)
        )
      )
    )
    (map check-implement-method (env-values (interface_-method-env intf)))
  )
  (map check-implement-interface interfaces)
)

(define (field-env->tenv field-env)
  (extend-tenv*/static-field (env-values field-env) (empty-env))
)
(define (extend-tenv*/static-field fields tenv)
  (foldl extend-tenv/static-field tenv fields)
)
(define (extend-tenv/static-field field tenv)
  (extend-env (static-field-name field) (static-field-type field) tenv)
)

(define (check-method-definition class-name method-decl tenv)
  (cases MethodDecl method-decl (MkMethodDecl (v signature body)
  (cases MethodSignature signature
    (MkMethodSignature (ret-t name params param-ts)
      (define body-env
        (extend-env self-var (TClass class-name)
          (extend-env host-var (TClass class-name)
            (extend-env* params param-ts tenv))))
      (assert-expr-type-in body ret-t body-env)
    )
  )))
)

(define (check-method-definitions class-name method-decls tenv)
  (define (check method-decl)
    (check-method-definition class-name method-decl tenv)
  )
  (map check method-decls)
)

; interface initialization

(define (extend-tenv*/AbsMethodDecl abs-decls tenv)
  (foldl extend-tenv/AbsMethodDecl tenv abs-decls)
)
(define (extend-tenv/AbsMethodDecl abs-decl tenv)
  (define mthd (AbsMethodDecl->static-method abs-decl))
  (extend-env (static-field-name mthd) mthd tenv)
)
(define (AbsMethodDecl->static-method abs-decl)
  (cases AbsMethodDecl abs-decl
    (MkAbsMethodDecl (signature) (MethodSignature->static-method signature))
  )
)
(define (MethodSignature->static-method signature)
  (cases MethodSignature signature
    (MkMethodSignature (ret-t name params param-ts)
      (static-method name (TFunc param-ts ret-t) (VPublic)))
  )
)

(define (<: t1 t2)
  (cases Type t1
    (TFunc (param-ts1 ret-t1) (cases Type t2
      (TFunc (param-ts2 ret-t2)
        (and
          (equal? (length param-ts1 param-ts2))
          (andmap <: param-ts2 param-ts1)
          (ret-t1 . <: . ret-t2))
      )
      (else false)
    ))
    (TClass (name1) (cases Type t2
      (TClass (name2)
        (define c1 (apply-class-env name1))
        (define c2 (apply-class-env name2))
        (cond
          ((interface_? c1) (and (interface_? c2) (equal? name1 name2)))
          ((interface_? c2) (c1 . implements? . c2))
          (else (<:-class c1 c2))
        )
      )
      (else false)
    ))
    (else (equal? t1 t2))
  ) ; cases Type t1
)

(define (apply-class-tenv/class class-name)
  (define result (apply-class-env class-name false))
  (unless (class_? result)
    (expect-some-type-error 'class class-name result)
  )
  result
)

(define (check-class tp expr)
  (define class-name (check-class-type tp expr))
  (apply-class-tenv/class class-name)
)

(define (check-class-type tp expr)
  (cases Type tp
    (TClass (name) name)
    (else (expect-some-type-error 'class expr tp))
  )
)

(define (check-class-like tp expr)
  (define class-name (check-class-type tp expr))
  (check-apply-class-env class-name)
)

(define (check-apply-class-env class-name)
  (define result (apply-class-env class-name false))
  (unless (class-like? result)
    (expect-some-type-error "class or interface" class-name result)
  )
  result
)

(define (apply-class-tenv/interface class-name)
  (define result (apply-class-env class-name false))
  (unless (interface_? result)
    (expect-some-type-error 'interface class-name result)
  )
  result
)

(define (expect-class-to-have-method cls method-name expr)
  (raise-user-error 'Class
    "Expect class ~a to have method ~a in ~v"
    (class_-name cls) method-name expr)
)

(define (check-class-method cls method-name expr)
  (define mthd (apply-class-method-tenv cls method-name))
  (unless mthd (expect-class-to-have-method cls method-name expr))
  mthd 
)

(define (check-method-call mthd args tenv)
  (check-call (static-field-type mthd) args tenv (static-field-name mthd))
)

(define (check-super-class cls expr)
  (define super-class (class_-super-class cls))
  (unless super-class
    (raise-user-error 'Class
      "Expect class ~a to have super class in ~v"
      (class_-name cls) expr)
  )
  super-class
)

(define (check-apply-tenv tenv var)
  (define tp (apply-env tenv var false))
  (unless tp
    (raise-user-error 'Type "Expect binding of ~a in ~v" var tenv)
  )
  tp
)

(define (check-host-class tenv expr)
  (define host-tp (check-apply-tenv tenv host-var))
  (check-class host-tp expr)
)

(define (check-related-types cls1 cls2 expr)
  (define (report-invalid-instance-of-unless b)
    (unless b
      (raise-user-error
        'Class "Type ~a and type ~a are unrelated in expression ~v"
        (class-name cls1) (class-name cls2) expr)
    )
  )
  (match* ((class_? cls1) (class_? cls2))
    ((#t #t)
      (report-invalid-instance-of-unless
        (or (<:-class cls1 cls2) (<:-class cls2 cls2)))
    )
    ((#f #t) (report-invalid-instance-of-unless (cls2 . implements? . cls1)))
    ((#t #f) (report-invalid-instance-of-unless (cls1 . implements? . cls2)))
    ((#f #f) (report-invalid-instance-of-unless false))
  )
)

(define (check-target-super-class cls super-name expr)
  (cond
    ((not cls)
      (raise-user-error 'Class
        "Expect class ~a to have super class ~a in ~v"
        (class_-name cls) super-name expr)
    )
    ((equal? (class_-name cls) super-name) cls)
    (else (check-target-super-class (class_-super-class cls) super-name expr))
  )
)

(define (expect-class-to-have-field cls field-name expr)
  (raise-user-error 'Class
    "Expect class ~a to have field ~a in ~v"
    (class_-name cls) field-name expr)
)

(define (check-class-field cls field-name expr)
  (define the-field (apply-class-field-tenv cls field-name))
  (unless the-field
    (expect-class-to-have-field cls field-name expr)
  )
  the-field
)

(define (type-of-program program)
  (cases Program program
    (MkProgram (class-decls expr)
      (initialize-class-tenv!)
      (extend-class-tenv*!/decls class-decls)
      (type-of expr (empty-env))
    )
  )
)

; (require racket/trace)
; (trace check-method-call)
