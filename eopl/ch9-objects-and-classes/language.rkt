#lang racket

(provide (all-defined-out))

(require "../eopl.rkt")

(sllgen:define oo-syntax '(
  (Program ((arbno ClassDecl) Expression) MkProgram)

  (Expression (number) Num)
  (Expression (identifier) Var)
  (Expression ("-" "(" Expression "," Expression ")") Diff)
  (Expression ("+" "(" Expression "," Expression ")") Plus)
  (Expression ("zero?" "(" Expression ")") Zero?)
  (Expression ("if" Expression "then" Expression "else" Expression) If)

  (Expression
    ("let" (arbno identifier "=" Expression) "in" Expression)
    Let)

  (Expression ("(" Expression (arbno Expression) ")") Call)

  (Expression
    ("proc" "(" (separated-list identifier ":" Type ",") ")" Expression)
    Proc)

  (Expression ("letrec" (arbno LetrecDef) "in" Expression) Letrec)
  (LetrecDef
    (Type identifier "(" (separated-list identifier ":" Type ",") ")"
     "=" Expression)
    MkLetrecDef)

  (Expression ("nil" "[" Type "]") Nil)
  (Expression
    ("list" "(" Expression "," (separated-list Expression ",") ")")
    List)

  (Expression ("begin" (separated-list Expression ";") "end") Begin_)

  (Expression ("set" identifier "=" Expression) Set)

  (Type ("(" Type "->" Type ")") TFunc)
  (Type ("int") TInt)
  (Type ("bool") TBool)
  (Type ("unit") TUnit)
  (Type ("list" Type) TList)

  ;; object oriented programming
  (ClassDecl
    ("class" identifier
      "extends" identifier
      (arbno "implements" identifier)
      (arbno FieldDecl)
      (arbno MethodDecl))
    CDeclClass)

  (ClassDecl
    ("interface" identifier (arbno AbsMethodDecl))
    CDeclInterface)

  (FieldDecl ("field" Visibility Type identifier) MkFieldDecl)

  (MethodDecl ("method" Visibility MethodSignature Expression) MkMethodDecl)
  (AbsMethodDecl ("method" MethodSignature) MkAbsMethodDecl)

  (MethodSignature
    (Type identifier "(" (separated-list identifier ":" Type ",") ")")
    MkMethodSignature)

  (Expression ("self") Self)

  (Expression ("new" identifier "(" (separated-list Expression ",") ")") New)

  (Expression
    ("send" Expression identifier "(" (separated-list Expression ",") ")")
    Send)
  (Expression
    ("super" identifier "(" (separated-list Expression ",") ")")
    Super)

  ; ex 9.6. instance of
  (Expression ("instance-of" Expression identifier) InstanceOf)

  ; ex 9.8. field reference
  (Expression ("field-get" Expression identifier) FieldGet)
  (Expression ("field-set" Expression identifier "=" Expression) FieldSet)

  ; ex 9.9. super object field reference
  (Expression ("super-field-get" identifier) SuperFieldGet)
  (Expression ("super-field-set" identifier "=" Expression) SuperFieldSet)

  ; ex 9.10. named static dispatch
  (Expression
    ("send-to" identifier
      Expression identifier "(" (separated-list Expression ",") ")")
    SendTo)

  ; ex 9.11. ex 9.12. field visibility
  (Visibility ("public") VPublic)
  (Visibility ("private") VPrivate)
  (Visibility ("protected") VProtected)

  (Expression ("cast" Expression identifier) Cast)

  (Type (identifier) TClass)
  (Type ("list" Type) TList)
))

(sllgen:make-define-datatypes eopl:lex-spec oo-syntax)
