#lang racket

(require "../eopl.rkt")
(provide (all-defined-out))

(sllgen:define modules-syntax '(
  (Program ((arbno ModuleDef) Expression) MkProgram)

  (Expression (number) Num)
  (Expression (identifier) Var)
  (Expression ("-" "(" Expression "," Expression ")") Diff)
  (Expression ("zero?" "(" Expression ")") Zero?)
  (Expression ("if" Expression "then" Expression "else" Expression) If)

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

  (Type ("bool") TBool)
  (Type ("int") TInt)
  (Type ("(" (separated-list Type ",") "->" Type ")") TFunc)

  ;; module
  (Type ("[" (arbno MDeclaration) "]") TModule)

  (ModuleDef
    ("module" identifier "interface" ModuleInterface "body" ModuleBody)
    MkModuleDef)

  (ModuleInterface ("[" (arbno MDeclaration) "]") MkModuleInterface)
  (MDeclaration (identifier ":" Type) MkMDeclaration)

  (ModuleBody ("[" (arbno MDefinition) "]") MkModuleBody)
  (MDefinition (identifier "=" Expression) MkMDefinition)

  (Expression ("from" identifier "take" identifier) QualifiedVar)
))

(sllgen:make-define-datatypes eopl:lex-spec modules-syntax)

