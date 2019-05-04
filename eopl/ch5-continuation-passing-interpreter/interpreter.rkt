#lang racket

(require "data.rkt")
(require "../eopl.rkt")
(require (submod "../ch4-state/store.rkt" global-mutable))
(require "cont.rkt")

(sllgen:define syntax-spec
  '((Program (Expression) a-program)

    (Expression (number) Num)
    (Expression (identifier) Var)
    (Expression ("-" "(" Expression "," Expression ")") Diff)
    (Expression ("zero?" "(" Expression ")") Zero?)
    (Expression ("not" "(" Expression ")") Not)
    (Expression ("if" Expression "then" Expression "else" Expression) If)

    (Expression
      ("proc" "(" (separated-list identifier ",") ")" Expression)
      Proc)

    (ProcDef
      (identifier "(" (separated-list identifier ",") ")"
        "=" Expression )
      MkProcDef)

    (Expression ("letrec" ProcDef (arbno ProcDef) "in" Expression) Letrec)

    ; ex 5.5.
    ; ex 5.6. list support
    (Expression ("nil") Nil)
    (Expression ("cons" "(" Expression "," Expression ")") Cons)
    (Expression ("list" "(" (separated-list Expression ",") ")") List)

    ; ex 5.3.
    ; ex 5.4.
    ; ex 5.7. multi-declaration let
    (Expression
      ("let" (arbno identifier "=" Expression) "in" Expression)
      Let)

    ; ex 5.8. multi-parameter procedure
    (Expression ("(" Expression (arbno Expression) ")") Call)

    ; ex 5.9. implicit references
    (Expression ("set" identifier "=" Expression) Set)

    ; ex 5.11. begin
    (Expression ("begin" (separated-list Expression ";") "end") Begin_)
  )
)

(sllgen:make-define-datatypes eopl:lex-spec syntax-spec)
(define parse (sllgen:make-string-parser eopl:lex-spec syntax-spec))

(define (value-of-program pgm)
  (cases Program pgm
    (a-program (expr)
      (initialize-store!)
      (expval->val (trampoline (value-of/k expr (empty-env) (end-cont))))
    )
  )
)

; bounce : expval + () -> bounce
; trampoline : bounce -> expval
(define (trampoline bounce)
  (if (expval? bounce)
    bounce
    (trampoline (bounce))
  )
)

(define (value-of/k expr env cont)
  (define (return v) (apply-cont cont v))
  (cases Expression expr
    (Num (n) (return (num-val n)))
    (Var (var) (return (deref (apply-env env var))))
    (Proc (params body)
      (return (make-procedure-val params body env))
    )
    (Letrec (procdef procdefs body)
      (eval-letrec/k (cons procdef procdefs) body env cont)
    )
    (Not (expr)
      (value-of/k expr env (λ (val)
        (return (bool-val (not (expval->bool val))))
      ))
    )
    (Zero? (expr)
      (value-of/k expr env (λ (val)
        (return (bool-val (zero? (expval->num val))))
      ))
    )
    (If (test texpr fexpr)
      (value-of/k test env (λ (val)
        (if (expval->bool val)
          (value-of/k texpr env cont)
          (value-of/k fexpr env cont))
      ))
    )
    (Diff (lhs rhs)
      (value-of/k lhs env (λ (v1)
        (value-of/k rhs env (λ (v2)
          (return (num-val (- (expval->num v1) (expval->num v2))))
        ))
      ))
    )
    ; ex 5.5. ex 5.6.
    (Nil () (return (list-val null)))
    (Cons (head tail)
      (value-of/k head env (λ (h)
        (value-of/k tail env (λ (t)
          (return (list-val (cons h (expval->list t))))
        ))
      ))
    )
    (List (exprs)
      (values-of/k exprs env (λ (vals) (return (list-val vals))))
    )

    ; ex 5.7.
    (Let (vars exprs body)
      (values-of/k exprs env (λ (vals)
        (value-of/k body (extend-env* vars (map newref vals) env) cont)
      ))
    )
    
    ; ex 5.8.
    (Call (operator operands)
      (value-of/k operator env (λ (proc)
        (values-of/k operands env (λ (args)
          (apply-procedure/k (expval->proc proc) (map newref args) cont)
        ))
      ))
    )

    ; ex 5.9.
    ; ex 5.10. Not keeping environment in continuation
    (Set (ident expr)
      (let ((ref (apply-env env ident)))
        (value-of/k expr env (λ (val)
          (setref! ref val)
          (return (void-val))
        ))
      )
    )

    ; ex 5.11.
    (Begin_ (exprs)
      (values-of/k exprs env (λ (vals) (return (last vals))))
    )
  )
)

(define (eval-letrec/k recdefs expr env cont)
  (define (ProcDef->ProcInfo recdef)
    (cases ProcDef recdef
      (MkProcDef (var params body) (ProcInfo var params body))
    )
  )
  (define (make-rec-env recdefs env)
    (extend-env*-rec (map ProcDef->ProcInfo recdefs) env)
  )
  (let ((rec-env (make-rec-env recdefs env)))
    (value-of/k expr rec-env cont)
  )
)

; trampolined apply-procedure/k
(define (apply-procedure/k p args cont) (λ ()
  (match p ((Procedure params body env)
    (if (not (equal? (length args) (length params)))
      (error 'apply-procedure
        "procedure arity mismatch between ~a (formal args) and ~a (real args)"
        (length args) (length params))
      (value-of/k body (extend-env* params args env) cont)
    )
  ))
))

; helper for evaluating multiple values
(define (values-of/k exprs env cont)
  (define (values-of/k-impl acc exprs)
    (match exprs
      ((quote ()) (apply-cont cont (reverse acc)))
      ((cons expr exprs1)
        (value-of/k expr env (λ (v)
          (values-of/k-impl (cons v acc) exprs1)
        ))
      )
    )
  )
  (values-of/k-impl null exprs)
)

; ex 5.17. ex 5.19.
; The definition of `bounce` need not to be changed, since
; bounce : expval + () -> bounce 
; so wrapping arbitrary layer of "() -> " to bounce still produces bounce.

((sllgen:make-rep-loop "sllgen> " value-of-program
   (sllgen:make-stream-parser eopl:lex-spec syntax-spec)))
