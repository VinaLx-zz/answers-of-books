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

  ;; simple module
  (Type ("[" (arbno MDeclaration) "]") TModule)

  (Expression
    ("from" identifier "take" identifier (arbno "take" identifier))
    QualifiedVar)

  (ModuleDef
    ("module" identifier "interface" ModuleInterface "body" ModuleBody)
    MkModuleDef)

  (ModuleInterface ("[" (arbno MDeclaration) "]") MkModuleInterface)

  (ModuleBody ("[" (arbno MDefinition) "]") MBDefinitions)

  ; ex 8.5. let/letrec in module body
  (ModuleBody ("let" (arbno identifier "=" Expression) "in" ModuleBody) MBLet)
  (ModuleBody ("letrec" (arbno LetrecDef) "in" ModuleBody) MBLetrec)

  ; ex 8.6. ex 8.7. nested module definition
  (ModuleBody (ModuleDef ModuleBody) MBModule)

  ; opaque types
  (Type (identifier) TAlias)
  (Type ("from" identifier "take" identifier) TQualified)

  (MDeclaration (identifier ":" Type) MDecVar)
  (MDeclaration ("opaque" identifier) MDecOpaque)
  (MDeclaration ("transparent" identifier "=" Type) MDecTrans)

  (MDefinition (identifier "=" Expression) MDefVar)
  (MDefinition ("type" identifier "=" Type) MDefType)
))

(sllgen:make-define-datatypes eopl:lex-spec modules-syntax)

