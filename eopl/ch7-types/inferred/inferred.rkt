#lang racket

(provide (all-defined-out))
(require "../../eopl.rkt")

(sllgen:define inferred-syntax '(
  (Program (Expression) a-program)

  (Expression (number) Num)
  (Expression (identifier) Var)
  (Expression ("true") True)
  (Expression ("false") False)
  (Expression ("-" "(" Expression "," Expression ")") Diff)
  (Expression ("zero?" "(" Expression ")") Zero?)
  (Expression ("if" Expression "then" Expression "else" Expression) If)

  (OptionalType ("?") OInfer)
  (OptionalType (Type) OType)

  (Type ("bool") TBool)
  (Type ("int") TInt)
  (Type ("(" (separated-list Type ",") "->" Type ")") TFunc)

  (Type ("%tvar" number) TVar)

  ; ex 7.23. pair
  (Type ("pair" Type Type) TPair)

  (Expression ("newpair" "(" Expression "," Expression ")") NewPair)
  (Expression
    ("unpair" identifier identifier "=" Expression "in" Expression)
    Unpair)

  ; ex 7.24. extended let, proc, letrec, call
  (Expression
    ("let" (arbno identifier "=" Expression) "in" Expression)
    Let)

  (Expression
    ("proc" "(" (separated-list identifier ":" OptionalType ",") ")" Expression)
    Proc)

  (Expression ("(" Expression (arbno Expression) ")") Call)

  (LetrecDef
    (OptionalType identifier
     "(" (separated-list identifier ":" OptionalType ",") ")" "=" Expression)
    MkLetrecDef)

  (Expression
    ("letrec" (arbno LetrecDef) "in" Expression)
    Letrec)

  ; ex 7.25. nil
  (Type ("list" Type) TList)

  (Expression ("nil") Nil)
  (Expression ("list" "(" (separated-list Expression ",") ")") List)
  (Expression ("cons" "(" Expression "," Expression ")") Cons)
  (Expression ("car"  "(" Expression ")") Car)
  (Expression ("cdr"  "(" Expression ")") Cdr)
  (Expression ("nil?" "(" Expression ")") Nil?)

  ; ex 7.26. explicit reference
  (Type ("ref" Type) TRef)
  (Type ("unit") TUnit)

  (Expression ("newref" "(" Expression ")") NewRef)
  (Expression ("deref" "(" Expression ")") Deref)
  (Expression ("setref" "(" Expression "," Expression ")") SetRef)
))

(sllgen:make-define-datatypes eopl:lex-spec inferred-syntax)

(define (map-type-var t f)
  (define (recurse t) (map-type-var t f))
  (cases Type t
    (TInt  () (TInt))
    (TBool () (TBool))
    (TUnit () (TUnit))
    (TVar  (n) (f n))
    (TFunc (args-t ret-t)
      (TFunc (map recurse args-t) (recurse ret-t))
    )
    (TPair (t1 t2)  (TPair (recurse t1) (recurse t2)))
    (TList (elem-t) (TList (recurse elem-t)))
    (TRef  (elem-t) (TRef (recurse elem-t)))
  )
)

; fold-type-var : Type -> a -> (number -> a -> a) -> a
(define (fold-type-var t z f)
  (cases Type t
    (TInt  () z)
    (TBool () z)
    (TUnit () z)
    (TVar  (n) (f n z))
    (TFunc (args-t ret-t)
      (foldl (λ (t acc) (fold-type-var t acc f)) z (cons ret-t args-t))
    )
    (TPair (lt rt)  (fold-type-var rt (fold-type-var lt z f) f))
    (TList (elem-t) (fold-type-var elem-t z f))
    (TRef  (elem-t) (fold-type-var elem-t z f))
  )
)

(define (occur-in? vi t)
  (fold-type-var t false (λ (tvar occur)
    (or occur (equal? tvar vi))
  ))
)

; Type -> Int -> Type -> Type
(define (apply-subst from var to)
  (map-type-var from (λ (vi)
    (if (equal? var vi) to (TVar vi))
  ))
)

(define (apply-substs from substs)
  (map-type-var from (λ (vi)
    (match (assoc vi substs)
      ((cons vi t) t)
      (#f (TVar vi))
    )
  ))
)


(define (empty-substs) null)
(define (extend-substs vi t substs)
  (define subst-subst
    (match-lambda ((cons tv old-t)
      (cons tv (apply-subst old-t vi t))
    ))
  )
  (cons (cons vi t) (map subst-subst substs))
)

(define (assoc-substs vi substs)
  (assoc vi substs)
)

(define (no-occurrence-violation vi t expr)
  (raise-user-error 'unify
    "Type variable ~v occur in ~v of expression ~v"
    vi t expr)
)

(define (unification-failure t1 t2 expr)
  (raise-user-error 'unify
    "unification failure of type ~v and ~v of expression ~v"
    t1 t2 expr)
)

(define (unify t1 t2 substs expr)
  (cases Type t1
    (TVar (vi1) (unify-with-tvar vi1 t2 substs expr))
    (else (cases Type t2
      (TVar (vi2) (unify-with-tvar vi2 t1 substs expr))
      (else (unify-without-tvar t1 t2 substs expr))
    ))
  )
)

(define (unify-without-tvar t1 t2 substs expr)
  (cases Type t1
    (TInt () (cases Type t2
      (TInt () substs)
      (else (unification-failure t1 t2 expr))
    ))
    (TBool () (cases Type t2
      (TBool () substs)
      (else (unification-failure t1 t2 expr))
    ))
    (TUnit () (cases Type t2
      (TUnit () substs)
      (else (unification-failure t1 t2 expr))
    ))
    (TFunc (args-t1 ret-t1) (cases Type t2
      (TFunc (args-t2 ret-t2)
        (if (equal? (length args-t1) (length args-t2))
          (unify-many (cons ret-t1 args-t1) (cons ret-t2 args-t2) substs expr)
          (unification-failure t1 t2 expr)
        )
      )
      (else (unification-failure t1 t2 expr))
    ))
    (TPair (l1 r1) (cases Type t2
      (TPair (l2 r2) (unify-many (list l1 r1) (list l2 r2) substs expr))
      (else (unification-failure t1 t2 expr))
    ))
    (TList (elem-t1) (cases Type t2
      (TList (elem-t2) (unify elem-t1 elem-t2 substs expr))
      (else (unification-failure t1 t2 expr))
    ))
    (TRef (elem-t1) (cases Type t2
      (TRef (elem-t2) (unify elem-t1 elem-t2 substs expr))
      (else (unification-failure t1 t2 expr))
    ))
    (else (error 'unify-without-tvar "unsupported unify type ~v" t1))
  )
)

(define (unify-many ts1 ts2 substs expr)
  (match* (ts1 ts2)
    (((quote ()) (quote ())) substs)
    (((cons t1 ts1) (cons t2 ts2))
      (unify-many ts1 ts2 (unify t1 t2 substs expr) expr)
    )
  )
)
(define (repeat-unify ts t substs expr)
  (match ts
    ((quote ()) substs)
    ((cons t1 ts1) (repeat-unify ts1 t (unify t1 t substs expr) expr))
  )
)

(define (optional-type->type ot)
  (cases OptionalType ot
    (OInfer () (new-tvar))
    (OType (t) t)
  )
)

(define (new-tvar) (TVar (next-type-var-index)))

(define next-index 0)
(define (next-type-var-index)
  (begin0 next-index (set! next-index (add1 next-index)))
)

(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (type PolyType?) (env environment?))
)

(define (apply-env env qvar)
  (cases environment env
    (empty-env () (error 'apply-env "type binding of ~a not found" qvar))
    (extend-env (var val env2)
      (if (equal? var qvar) val (apply-env env2 qvar))
    )
  )
)
(define (extend-env/binding b env)
  (extend-env (car b) (cdr b) env)
)
(define (extend-env*/binding bs env)
  (foldl (λ (b acc) (extend-env/binding b acc)) env bs)
)
(define (extend-env* vars vals env)
  (extend-env*/binding (zip vars vals) env)
)

(define (type-of expr substs tenv)
  (cases Expression expr
    (True () (values (TBool) substs))
    (False () (values (TBool) substs))
    (Num (n) (values (TInt) substs))
    (Var (v) (values (instantiate-poly (apply-env tenv v)) substs))
    (Zero? (expr)
      (define-values (t substs1) (type-of expr substs tenv))
      (define rsubsts (unify t (TInt) substs1 expr))
      (values (TBool) rsubsts)
    )
    (Diff (lhs rhs)
      (define-values (lhs-t lhs-substs) (type-of lhs substs tenv))
      (define-values (rhs-t rhs-substs) (type-of rhs lhs-substs tenv))
      (define rsubsts
        (unify-many (list lhs-t rhs-t) (list (TInt) (TInt)) rhs-substs expr)
      )
      (values (TInt) rsubsts)
    )
    (If (test iftrue iffalse)
      (define-values (test-t test-substs) (type-of test substs tenv))
      (define-values (true-t true-substs) (type-of iftrue test-substs tenv))
      (define-values (false-t false-substs) (type-of iffalse true-substs tenv))
      (define rsubsts
        (unify-many
          (list test-t true-t) (list (TBool) false-t)
          false-substs expr)
      )
      (values true-t rsubsts)
    )
    (Let (vars vals body)
      (define-values (val-ts substs1) (types-of vals substs tenv))
      (define body-env
        (extend-env* vars (map (generalize substs1) val-ts) tenv))
      (type-of body substs1 body-env)
    )
    (Proc (params otypes body)
      (define param-ts (map optional-type->type otypes))
      (define body-env (extend-env* params (map Mono param-ts) tenv))
      (define-values (ret-t substs1) (type-of body substs body-env))
      (values (TFunc param-ts ret-t) substs1)
    )
    (Letrec (defs body)
      (define func-defs (map LetrecDef->FuncDef defs))
      (define letrec-names (map FuncDef-name func-defs))
      (define letrec-types (map type-of-funcdef func-defs))
      (define funcdef-common-env
        (extend-env* letrec-names (map Mono letrec-types) tenv))
      (define substs1 (unify-funcdefs func-defs substs funcdef-common-env))

      (define let-body-env
        (extend-env* letrec-names (map (generalize substs1) letrec-types) tenv))
      (type-of body substs1 let-body-env)
    )
    (Call (func args)
      (define-values (arg-ts args-substs) (types-of args substs tenv))
      (define-values (func-t func-substs) (type-of func args-substs tenv))
      (define ret-t (new-tvar))
      (define rsubsts (unify func-t (TFunc arg-ts ret-t) func-substs expr))
      (values ret-t rsubsts)
    )

    (NewPair (lexpr rexpr)
      (define-values (lt lsubsts) (type-of lexpr substs tenv))
      (define-values (rt rsubsts) (type-of rexpr lsubsts tenv))
      (values (TPair lt rt) rsubsts)
    )
    (Unpair (lvar rvar expr body)
      (define-values (lt rt) (values (new-tvar) (new-tvar)))
      (define-values (expr-t substs1) (type-of expr substs tenv))
      (define substs2 (unify expr-t (TPair lt rt) substs1 expr))
      (define body-env
        (extend-env* (list lvar rvar)
          (map (generalize substs2) (list lt rt)) tenv))
      (type-of body substs2 body-env)
    )
    (Nil () (values (TList (new-tvar)) substs))
    (List (exprs)
      (define elem-t (new-tvar))
      (define-values (expr-ts substs1) (types-of exprs substs tenv))
      (define rsubsts (repeat-unify expr-ts elem-t substs1 expr))
      (values (TList elem-t) rsubsts)
    )
    (Cons (head tail)
      (define-values (head-t head-substs) (type-of head substs tenv))
      (define-values (tail-t tail-substs) (type-of tail head-substs tenv))
      (define rsubsts (unify tail-t (TList head-t) tail-substs expr))
      (values tail-t rsubsts)
    )
    (Car (expr)
      (define elem-t (new-tvar))
      (define-values (expr-t substs1) (type-of expr substs tenv))
      (define rsubsts (unify expr-t (TList elem-t) substs1 expr))
      (values elem-t rsubsts)
    )
    (Cdr (expr)
      (define elem-t (new-tvar))
      (define-values (expr-t substs1) (type-of expr substs tenv))
      (define rsubsts (unify expr-t (TList elem-t) substs1 expr))
      (values (TList elem-t) rsubsts)
    )
    (Nil? (expr)
      (define-values (expr-t substs1) (type-of expr substs tenv))
      (define rsubsts (unify expr-t (TList (new-tvar)) substs1 expr))
      (values (TBool) rsubsts)
    )
    (NewRef (expr)
      (define-values (expr-t substs1) (type-of expr substs tenv))
      (values (TRef expr-t) substs1)
    )
    (Deref (expr)
      (define-values (expr-t substs1) (type-of expr substs tenv))
      (define elem-t (new-tvar))
      (define rsubsts (unify expr-t (TRef elem-t) substs1 tenv))
      (values elem-t rsubsts)
    )
    (SetRef (ref-expr val-expr)
      (define-values (ref-t substs1) (type-of ref-expr substs tenv))
      (define-values (val-t substs2) (type-of ref-expr substs1 tenv))
      (define rsubsts (unify ref-t (TRef val-t) substs2 ref-expr))
      (values (TUnit) rsubsts)
    )
  )
)

(define (types-of exprs substs tenv)
  (define (types-of-cps exprs substs f)
    (match exprs
      ((quote ()) (f null substs))
      ((cons expr exprs1)
        (define-values (tp substs1) (type-of expr substs tenv))
        (types-of-cps exprs1 substs1 (λ (types substs)
          (f (cons tp types) substs)
        ))
      )
    )
  )
  (types-of-cps exprs substs values)
)

(struct FuncDef (ret-t name params param-ts body))

(define (LetrecDef->FuncDef def)
  (cases LetrecDef def (MkLetrecDef (ret-ot name params param-ots body)
    (FuncDef
      (optional-type->type ret-ot) name params
      (map optional-type->type param-ots) body)
  ))
)

(define (type-of-funcdef def)
  (match def ((FuncDef ret-t name params param-ts body)
    (TFunc param-ts ret-t)
  ))
)
(define (binding-of-funcdef def)
  (cons (FuncDef-name def) (type-of-funcdef def))
)
(define (unify-funcdef def substs tenv)
  (match def ((FuncDef ret-t name params param-ts body)
    (define-values (body-t substs1)
      (type-of body substs (extend-env* params (map Mono param-ts) tenv))
    )
    (unify ret-t body-t substs1 body)
  ))
)
(define (unify-funcdefs defs substs tenv)
  (match defs
    ((quote ()) substs)
    ((cons def defs)
      (unify-funcdefs defs (unify-funcdef def substs tenv) tenv)
    )
  )
)

(define (type-of-program program)
  (cases Program program
    (a-program (expr)
      (with-handlers
        ((exn:fail:user?
          (match-lambda ((exn:fail:user message _)
            (printf "~a\n" message)
          )))
        )
        (define-values (t substs) (type-of expr (empty-substs) (empty-env)))
        (pretty-print (apply-substs t substs))
        (void)
      )
    )
  )
)


; ex 7.17. ex 7.18.
(module* subst-exercise #f
  (define (extend-substs vi t substs) (cons (cons vi t) substs))

  (define (apply-substs from substs)
    (foldr
      (λ (subst acc) (apply-subst acc (car subst) (cdr subst)))
      from substs)
  )
)

; ex 7.20. calling apply-substs only on type variable
(define (unify-with-tvar vi1 t2 substs expr)
  (define (unify-substed-tvar vi1 t2)
    (cases Type t2
      (TVar (vi2)
        (if (equal? vi1 vi2) substs (extend-substs vi1 t2 substs))
      )
      (else
        (if (occur-in? vi1 t2)
          (no-occurrence-violation vi1 t2 expr)
          (extend-substs vi1 t2 substs)
        )
      )
    ) ; cases t2
  ) ; unify-substed-tvar
  (define substed1 (apply-substs (TVar vi1) substs))
  (cases Type substed1
    (TVar (svi1) (unify-substed-tvar svi1 (apply-substs t2 substs)))
    (else (unify substed1 t2 substs expr))
  )
)

; ex 7.28. ex 7.29. polymorphism
(define-datatype PolyType PolyType?
  (Mono (t Type?))
  (Poly (tparam number?) (poly1 PolyType?))
)

; generalize : Type -> substs -> PolyType
(define ((generalize substs) t)
  (define substed-t (apply-substs t substs))
  (define type-vars (collect-type-vars substed-t))
  (foldr (λ (vi poly)
    (if (assoc-substs vi substs) poly (Poly vi poly))
  ) (Mono substed-t) type-vars)
)

; collect-type-vars : Type -> List number
(define (collect-type-vars t) (fold-type-var t null cons))

; instantiate-poly : PolyType -> Type
(define (instantiate-poly poly)
  (cases PolyType poly
    (Mono (tp) tp)
    (Poly (tparam poly)
      (define instantiated-tvar (new-tvar))
      (map-type-var (instantiate-poly poly) (λ (vi) 
        (if (equal? tparam vi) instantiated-tvar (TVar vi))
      ))
    )
  )
)

((sllgen:make-rep-loop "inferred> " type-of-program
   (sllgen:make-stream-parser eopl:lex-spec inferred-syntax)))
