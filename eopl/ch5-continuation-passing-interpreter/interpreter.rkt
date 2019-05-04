#lang racket

(require "data.rkt")
(require "../eopl.rkt")
(require "cont.rkt")

(sllgen:define syntax-spec
  '((Program (Expression) a-program)

    (Expression (number) Num)
    (Expression (identifier) Var)
    (Expression ("-" "(" Expression "," Expression ")") Diff)
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
        "=" Expression )
      MkProcDef)

    (Expression ("letrec" ProcDef (arbno ProcDef) "in" Expression) Letrec)
  )
)

(sllgen:make-define-datatypes eopl:lex-spec syntax-spec)
(define parse (sllgen:make-string-parser eopl:lex-spec syntax-spec))

(define (value-of-program pgm)
  (cases Program pgm
    (a-program (expr)
      (expval->val (value-of/k expr (empty-env) (end-cont)))
    )
  )
)

(define (value-of/k expr env cont)
  (cases Expression expr
    (else 'todo)
  )
)

((sllgen:make-rep-loop "sllgen> " value-of-program
   (sllgen:make-stream-parser eopl:lex-spec syntax-spec)))
