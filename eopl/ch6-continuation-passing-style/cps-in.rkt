#lang racket

(provide (all-defined-out))
(require "../eopl.rkt")

(sllgen:define cps-in-syntax '(
  (Program (Expression) a-program)
  (Expression (number) Num)
  (Expression (identifier) Var)
  (Expression ("-" "(" Expression "," Expression ")") Diff)
  (Expression ("+" "(" (separated-list Expression "," ) ")") Sum)
  (Expression ("zero?" "(" Expression ")") Zero?)
  (Expression ("if" Expression "then" Expression "else" Expression) If)
  (Expression
    ("let" (arbno identifier "=" Expression) "in" Expression)
    Let)

  (Expression ("(" Expression (arbno Expression) ")") Call)

  (Expression
    ("proc" "(" (separated-list identifier ",") ")" Expression)
    Proc)

  (ProcDef
    (identifier "(" (separated-list identifier ",") ")"
      "=" Expression)
    MkProcDef)

  (Expression ("letrec" (arbno ProcDef) "in" Expression) Letrec)

  ; computational effects
  (Expression ("print" "(" Expression ")") Print)

  (Expression ("newref" "(" Expression ")") NewRef)
  (Expression ("deref" "(" Expression ")") Deref)
  (Expression ("setref" "(" Expression "," Expression ")") SetRef)

  ; ex 6.36.
  (Expression ("begin" (separated-list Expression ";") "end") Begin_)

  ;; non-local control

  ; ex 6.39. implement letcc and throw
  (Expression ("letcc" identifier "in" Expression) LetCC)
  (Expression ("throw" Expression "to" Expression) Throw)

  ; ex 6.40. implement try catch and raise
  (Expression
    ("try" Expression "catch" "(" identifier ")" Expression)
    TryCatch)

  (Expression ("raise" Expression) Raise)
))

; ex 6.19
; a SOUND (but not complete) tailformed expression predicate
; The predicate conforms the syntax of "cps-out", which doesn't accept
; `let a = <SimpleExpr> in <SimpleExpr>` and similar expression as a simple
; expression, so that it considers `-(let a = 1 in a, 1)` to be not tailformed.
; So that it is only a sound predicate but not complete.
(define (is-tailform expr)
  (cases Expression expr
    (If (test iftrue iffalse)
      (and (is-tailform-simple test) (is-tailform iftrue) (is-tailform iffalse))
    )
    (Let (vars vals body)
      (and (andmap is-tailform-simple vals) (is-tailform body))
    )
    (Letrec (defs body)
      (and (is-tailform body) (andmap def-is-tailform defs))
    )
    (Call (proc args) (andmap is-tailform-simple (cons proc args)))

    (Print (expr) (is-tailform expr))

    (else (is-tailform-simple expr))
  )
)

(define (def-is-tailform proc-def)
  (cases ProcDef proc-def
    (MkProcDef (name params body) (is-tailform body))
  )
)

(define (is-tailform-simple expr)
  (cases Expression expr
    (Num (n) true)
    (Var (v) true)
    (Diff (lhs rhs) (and (is-tailform-simple lhs) (is-tailform-simple rhs)))
    (Sum (exprs) (andmap is-tailform-simple exprs))
    (Zero? (expr) (is-tailform-simple expr))
    (Proc (params body) (is-tailform body))
    (else false)
  )
)

(sllgen:make-define-datatypes eopl:lex-spec cps-in-syntax)
(define cps-in:parse (sllgen:make-string-parser eopl:lex-spec cps-in-syntax))
