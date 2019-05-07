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
))

(sllgen:make-define-datatypes eopl:lex-spec cps-in-syntax)
(define cps-in:parse (sllgen:make-string-parser eopl:lex-spec cps-in-syntax))
