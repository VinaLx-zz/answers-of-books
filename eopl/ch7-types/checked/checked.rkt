#lang racket

(require "../../eopl.rkt")
(provide (all-defined-out))

(sllgen:define checked-syntax
  '((Program (Expression) a-program)

    (Expression (number) Num)
    (Expression (identifier) Var)
    (Expression ("-" "(" Expression "," Expression ")") Diff)
    (Expression ("zero?" "(" Expression ")") Zero?)
    (Expression ("if" Expression "then" Expression "else" Expression) If)

    ; ex 7.5. extended let/proc/call/letrec
    (Expression
      ("let" (arbno identifier "=" Expression) "in" Expression)
      Let)

    (Expression
      ("proc" "(" (separated-list identifier ":" Type ",") ")" Expression)
      Proc)

    (Expression ("(" Expression (arbno Expression) ")") Call)

    (LetrecDef
      (Type identifier "(" (separated-list identifier ":" Type ",") ")"
        "=" Expression)
      MkLetrecDef)

    (Expression
      ("letrec" (arbno LetrecDef) "in" Expression)
      Letrec)

    ; ex 7.6 assignment
    (Expression ("set" identifier "=" Expression) Set)

    (Type ("bool") TBool)
    (Type ("int") TInt)
    (Type ("unit") TUnit)
    (Type ("(" (separated-list Type ",") "->" Type ")") TFunc)

    ; ex 7.8 pair
    (Type ("pair" Type Type) TPair)

    (Expression ("newpair" "(" Expression "," Expression ")") NewPair)
    (Expression
      ("unpair" identifier identifier "=" Expression "in" Expression)
      Unpair)

    ; ex 7.9. list
    (Type ("list" Type) TList)
    
    (Expression ("nil" "[" Type "]") Nil)
    (Expression ("cons" "(" Expression "," Expression ")") Cons)
    (Expression ("list" "(" Expression (arbno "," Expression) ")") List)
    (Expression ("null?" "(" Expression ")") Null?)
    (Expression ("car" "(" Expression ")") Car)
    (Expression ("cdr" "(" Expression ")") Cdr)

    ; ex 7.10. ref
    (Type ("ref" Type) TRef)
    
    (Expression ("newref" "(" Expression ")") NewRef)
    (Expression ("deref" "(" Expression ")") Deref)
    (Expression ("setref" "(" Expression "," Expression ")") SetRef)
  )
)

(sllgen:make-define-datatypes eopl:lex-spec checked-syntax)

(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val Type?) (env environment?))
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
    (Zero? (expr)
      (assert-expr-type expr (TInt))
      (TBool)
    )
    
    ; ex 7.5.
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

    ; ex 7.6.
    (Set (var expr)
      (define var-tp (apply-env tenv var))
      (assert-expr-type expr var-tp)
      (TUnit)
    )

    ; ex 7.7. check the type of test before checking the types of branches
    (If (test iftrue iffalse)
      (assert-expr-type test (TBool))
      (define t-tp (tp-of iftrue))
      (assert-expr-type iffalse t-tp)
      t-tp
    )

    ; ex 7.8. pair
    (NewPair (fst snd)
      (define fst-tp (tp-of fst))
      (define snd-tp (tp-of snd))
      (TPair fst-tp snd-tp)
    )
    (Unpair (fst-var snd-var pexpr body)
      (define tp (tp-of pexpr))
      (cases Type tp
        (TPair (fst-tp snd-tp)
          (define body-env
            (extend-env* (list fst-var snd-var) (list fst-tp snd-tp) tenv))
          (type-of body body-env)
        )
        (else (expect-some-type-error 'pair pexpr tp))
      )
    )

    ; ex 7.9. list
    (Nil (type) (TList type))
    (Cons (head tail)
      (define list-tp (tp-of tail))
      (assert-expr-type head (extract-list-elem list-tp tail))
      list-tp
    )
    (List (head rests)
      (define elem-tp (tp-of head))
      (map (λ (elem) (assert-expr-type elem elem-tp)) rests)
      (TList elem-tp)
    )
    (Null? (lexpr)
      (extract-list-elem (tp-of lexpr) lexpr)
      (TBool)
    )
    (Car (lexpr)
      (extract-list-elem (tp-of lexpr) lexpr)
    )
    (Cdr (lexpr)
      (TList (extract-list-elem (tp-of lexpr) lexpr))
    )

    ; ex 7.10. ref
    (NewRef (expr) (TRef (tp-of expr)))
    (Deref (expr)
       (extract-ref-elem (tp-of expr) expr)
    )
    (SetRef (rexpr vexpr)
      (define elem-tp (extract-ref-elem (tp-of rexpr) rexpr))
      (assert-expr-type vexpr elem-tp)
      (TUnit)
    )

  ) ; cases 
)

(define (expect-some-type-error sometype expr t)
  (raise-user-error
    'TypeError "Expect ~v to have ~a type, but found ~v"
    expr sometype t)
)

; ex 7.5.

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

(define (type-of-program program)
  (cases Program program
    (a-program (expr)
      (with-handlers
        ((exn:fail:user?
          (match-lambda ((exn:fail:user message _)
            (printf "~a\n" message)
          )))
        )
        (define t (type-of expr (empty-env)))
        (printf "~v\n" t)
        (void)
      )
    )
  )
)

; ex 7.9.

(define (extract-list-elem tp expr)
  (cases Type tp
    (TList (elem-tp) elem-tp)
    (else (expect-some-type-error 'list expr tp))
  )
)

; ex 7.10.

(define (extract-ref-elem tp expr)
  (cases Type tp
    (TRef (elem-tp) elem-tp)
    (else (expect-some-type-error 'ref expr tp))
  )
)


((sllgen:make-rep-loop "checked> " type-of-program
   (sllgen:make-stream-parser eopl:lex-spec checked-syntax)))
