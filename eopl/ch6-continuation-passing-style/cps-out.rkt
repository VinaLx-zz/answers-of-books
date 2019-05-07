#lang racket

(provide (all-defined-out))
(require "data.rkt")
(require "../eopl.rkt")

(sllgen:define cps-out-syntax '(
  (Program (TailFormExpr) a-program)

  ; Tail Form Expression 
  (TailFormExpr (SimpleExpr) TfSimple)

  (TailFormExpr
    ("let" (arbno identifier "=" SimpleExpr) "in" TailFormExpr)
    TfLet)

  (TfProcDef
    (identifier "(" (separated-list identifier ",") ")" "=" TailFormExpr)
    MkTfProcDef)

  (TailFormExpr
    ("letrec" (arbno TfProcDef) "in" TailFormExpr)
    TfLetrec)

  (TailFormExpr
    ("if" SimpleExpr "then" TailFormExpr "else" TailFormExpr)
    TfIf)

  (TailFormExpr ("(" SimpleExpr (arbno SimpleExpr) ")") TfCall)

  ; Simple Expression
  (SimpleExpr (number) SNum)
  (SimpleExpr (identifier) SVar)
  (SimpleExpr ("-" "(" SimpleExpr "," SimpleExpr ")") SDiff)
  (SimpleExpr ("+" "(" (separated-list SimpleExpr "," ) ")") SSum)
  (SimpleExpr ("zero?" "(" SimpleExpr ")") SZero?)
  (SimpleExpr
    ("proc" "(" (separated-list identifier "," )")" TailFormExpr)
    SProc)
))

(sllgen:make-define-datatypes eopl:lex-spec cps-out-syntax)
(define cps-out:parse (sllgen:make-string-parser eopl:lex-spec cps-out-syntax))

; 6.14. complete the definition for value-of-program (here is eval-cps-out)
(define (eval-cps-out program)
  (cases Program program
    (a-program (tfexpr)
      (expval->val (eval-tailform tfexpr (empty-env)))
    )
  )
)

; ex 6.15. remove the continuation parameter altogether
(define (eval-tailform tfexpr env)
  (define (eval e) (eval-tailform e env))
  (define (seval e) (eval-simple e env))
  (cases TailFormExpr tfexpr
    (TfSimple (expr) (seval expr))
    (TfLet (vars vals body)
      (eval-tailform body (extend-env* vars (map seval vals) env))
    )
    (TfLetrec (defs body) (eval-letrec defs body env))
    (TfIf (test iftrue iffalse)
      (if (expval->bool (seval test))
        (eval iftrue) (eval iffalse)
      )
    )
    (TfCall (proc args)
      (apply-procedure (expval->proc (seval proc)) (map seval args))
    )
  )
)

(define (eval-letrec recdefs expr env)
  (define (ProcDef->ProcInfo recdef)
    (cases TfProcDef recdef
        (MkTfProcDef (var params body) (ProcInfo var params body))
    )
  )
  (define (make-rec-env recdefs env)
    (extend-env*-rec (map ProcDef->ProcInfo recdefs) env)
  )
  (let ((rec-env (make-rec-env recdefs env)))
    (eval-tailform expr rec-env)
  )
)

(define (apply-procedure p args)
  (match p ((Procedure vars body env)
    (define nargs (length args))
    (define nparams (length vars))
    (if (not (equal? nargs nparams))
      (error 'apply-procedure
        "incorrect number of arguments: (~a), should be ~a" nparams nargs)
      (eval-tailform body (extend-env* vars args env))
    )
  ))
)

; ex 6.11
(define (eval-simple expr env)
  (define (eval e) (eval-simple e env))
  (cases SimpleExpr expr
    (SNum (n) (num-val n))
    (SVar (var) (apply-env env var))
    (SDiff (lhs rhs)
      (num-val
        (- (expval->num (eval lhs)) (expval->num (eval rhs)))
      )
    )
    (SSum (exprs)
      (num-val (apply + (map (compose expval->num eval) exprs)))
    )
    (SZero? (expr) (bool-val (zero? (expval->num (eval expr)))))
    (SProc (params body) (make-procedure-val params body env))
  )
)

; ((sllgen:make-rep-loop "cps-out> " eval-cps-out
   ; (sllgen:make-stream-parser eopl:lex-spec cps-out-syntax)))
