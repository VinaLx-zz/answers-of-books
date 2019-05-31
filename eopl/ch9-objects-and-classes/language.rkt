#lang racket

(provide (all-defined-out))

(require "../eopl.rkt")

(sllgen:define oo-syntax '(
  (Program ((arbno ClassDecl) Expression) MkProgram)

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
    ("proc" "(" (separated-list identifier ":" Type ",") ")" Expression)
    Proc)

  (Expression ("letrec" (arbno ProcDef) "in" Expression) Letrec)
  (ProcDef
    (Type identifier "(" (separated-list identifier ":" Type ",") ")"
     "=" Expression)
    MkProcDef)

  (Expression ("begin" (separated-list Expression ";") "end") Begin_)

  (Expression ("set" identifier "=" Expression) Set)

  (Type ("(" Type "->" Type ")") TFunc)
  (Type ("int") TInt)
  (Type ("bool") TBool)
  (Type ("unit") TUnit)

  ;; object oriented programming
  (ClassDecl
    ("class" identifier
      "extends" identifier
      (arbno "implements" identifier)
      (arbno "field" identifier)
      (arbno MethodDecl))
    CDeclClass)

  (ClassDecl
    ("interface" identifier (arbno AbsMethodDecl))
    CDeclInterface)

  (MethodDecl ("method" MethodSignature Expression) MkMethodDecl)
  (AbsMethodDecl ("method" MethodSignature) MkAbsMethodDecl)

  (MethodSignature
    (identifier "(" (separated-list identifier ":" Type ",") ")")
    MkMethodSignature)

  (Expression ("new" identifier "(" (separated-list Expression ",") ")") New)

  (Expression
    ("send" Expression identifier "(" (separated-list Expression ",") ")")
    Send)
  (Expression
    ("super" identifier "(" (separated-list Expression ",") ")")
    Super)

  (Expression ("instance-of" Expression identifier) InstanceOf)
  (Expression ("cast" Expression identifier) Cast)
  (Expression ("self") Self)

  (Type (identifier) TClass)
  (Type ("list" Type) TList)
))

(sllgen:make-define-datatypes eopl:lex-spec oo-syntax)
