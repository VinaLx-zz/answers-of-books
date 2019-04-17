#lang racket

(require "procedure.rkt")
(require (only-in eopl define-datatype cases))
(require "../sllgen.rkt")

(provide (all-defined-out))

(sllgen:define let-syn-spec
  '((Program (Expression) a-program)

    (Expression (number) Num)
    (Expression (identifier) Var)
    (Expression ("-" "(" Expression "," Expression ")") Diff)
    (Expression ("zero?" "(" Expression ")") Zero?)
    (Expression ("if" Expression "then" Expression "else" Expression) If)

    ; ex 3.6 minus
    (Expression ("minus" "(" Expression ")") Minus)

    ; ex 3.7 plus / multiplication / quotient
    (Expression ("+" "(" Expression "," Expression ")") Plus)
    (Expression ("*" "(" Expression "," Expression ")") Mult)
    (Expression ("/" "(" Expression "," Expression ")") Div)

    ; ex 3.8 order
    (Expression ("=" "(" Expression "," Expression ")") Equal?)
    (Expression ("<" "(" Expression "," Expression ")") Less?)
    (Expression (">" "(" Expression "," Expression ")") Greater?)

    ; ex 3.9 list
    (Expression ("cons" "(" Expression "," Expression ")") Cons)
    (Expression ("nil") Nil)

    ; ex 3.10 List
    (Expression ("list" "(" (separated-list Expression ",") ")") List)

    ; ex 3.12 Cond
    (Expression ("cond" (arbno Expression "==>" Expression) "end") Cond)

    ; ex 3.13. and ex 3.14.
    ; omitted due to the strange requirements

    ; ex 3.15 print
    (Expression ("print" "(" Expression ")") Print)

    ; ex 3.16 extended let
    (Expression
      ("let" (arbno identifier "=" Expression) "in" Expression)
      Let)

    ; ex 3.17 let*
    (Expression
      ("let*" (arbno identifier "=" Expression) "in" Expression)
      Let*)

    ; ex 3.18 unpack
    (Expression
      ("unpack" (arbno identifier) "=" Expression "in" Expression)
      Unpack)

    ;; proc

    (Expression ("(" Expression (arbno Expression) ")") Call)

    ; ex 3.21
    (Expression
      ("proc" "(" (separated-list identifier ",") ")" Expression)
      Proc)

    ; ex 3.19
    (ProcDef
      (identifier "(" (separated-list identifier ",") ")"
        "=" Expression )
      MkProcDef)

    (Expression
      ("letproc" ProcDef (arbno ProcDef) "in" Expression)
      Letproc)

    ;; letrec

    ; ex 3.31. ex 3.32. ex 3.33.
    (Expression ("letrec" ProcDef (arbno ProcDef) "in" Expression) Letrec)
  )
)

(sllgen:make-define-datatypes eopl:lex-spec let-syn-spec)
(define parse (sllgen:make-string-parser eopl:lex-spec let-syn-spec))

(define (init-env) (empty-env))

(define (value-of-program pgm)
  (cases Program pgm
    (a-program (expr) (expval->val (value-of expr (init-env))))
  )
)

(define (value-of expr env)
  (cases Expression expr
    (Num (n) (num-val n))
    (Diff (lhs rhs) (int-binary-int lhs rhs - env))
    (Zero? (expr)
      (bool-val (zero? (expval->num (value-of expr env))))
    )
    (If (test texpr fexpr)
      (if (expval->bool (value-of test env))
        (value-of texpr env)
        (value-of fexpr env)
      )
    )
    (Var (var) (apply-env env var))

    ; ex 3.6.
    (Minus (expr)
      (num-val (- (expval->num (value-of expr env))))
    )

    ; ex 3.7.
    (Plus (lhs rhs) (int-binary-int lhs rhs + env))
    (Mult (lhs rhs) (int-binary-int lhs rhs * env))
    (Div  (lhs rhs) (int-binary-int lhs rhs quotient env))

    ; ex 3.8.
    (Equal?   (lhs rhs) (int-binary-bool lhs rhs equal? env))
    (Greater? (lhs rhs) (int-binary-bool lhs rhs > env))
    (Less?    (lhs rhs) (int-binary-bool lhs rhs < env))

    ; ex 3.9.
    (Nil () (list-val null))
    (Cons (head tail)
      (list-val
        (cons (value-of head env)
              (expval->list (value-of tail env))))
    )
    ; ex 3.10.
    (List (exprs)
      (list-val (map (λ (expr) (value-of expr env)) exprs))
    )

    ; ex 3.12.
    (Cond (tests bodies) (value-of (Cond->If tests bodies) env))

    ; ex 3.15
    (Print (expr) (begin
      (display (expval->val (value-of expr env)))
      (num-val 1)
    ))

    ; ex 3.16
    (Let (vars vals body) (eval-let vars vals body env))

    ; ex 3.17
    (Let* (vars vals body) (value-of (Let*->Let vars vals body) env))

    ; ex 3.18
    (Unpack (idents val body)
      (let ((vals (expval->list (value-of val env))))
        (if (not (equal? (length idents) (length vals)))
          (error 'unpack "arity mismatch of identifiers and values")
          (value-of body (extend-env* idents vals env))
        )
      )
    )

    ;; proc

    ; ex 3.19.
    (Letproc (procdef procdefs expr)
      (let-values
        (((vars procs) (Letproc->Let (cons procdef procdefs) env)))
        (eval-let vars procs expr env)
      )
    )

    ; ex 3.21
    (Proc (params body) (make-procedure-val params body env))

    (Call (operator operands)
      (let ((proc (expval->proc (value-of operator env)))
            (args (map (λ (operand) (value-of operand env)) operands)))
        (apply-procedure proc args)
      )
    )

    ; ex 3.31.
    (Letrec (def defs expr) (eval-letrec (cons def defs) expr env))
  ) ; cases
) ; value-of

(define (eval-let vars vals body env)
  (let ((new-env
      (extend-env* vars (map (λ (val) (value-of val env)) vals) env)))
    (value-of body new-env)
  )
)

; ex 3.11. operator interpretation abstraction
(define (int-binary-int lhs rhs rkt-op env)
  (binary-op num-val expval->num lhs rhs rkt-op env)
)
(define (int-binary-bool lhs rhs rkt-op env)
  (binary-op bool-val expval->num lhs rhs rkt-op env)
)

(define (binary-op to-expval from-expval lhs rhs rkt-op env)
  (to-expval
    (rkt-op (from-expval (value-of lhs env))
            (from-expval (value-of rhs env))))
)

; ex 3.12.
(define (Cond->If tests bodies)
  (if (null? tests) (error 'Cond->If "non-exhausted-matches")
    (let ((test   (car tests)) (body    (car bodies))
          (tests1 (cdr tests)) (bodies1 (cdr bodies)))
      (If test body (Cond tests1 bodies1))
    )
  )
)

; ex 3.17.
(define (Let*->Let vars vals body)
  (if (null? vars) body
    (let ((var (car vars)) (val (car vals))
          (vars1 (cdr vars)) (vals1 (cdr vals)))
      (Let (list var) (list val) (Let*->Let vars1 vals1 body))
    )
  )
)

;; proc
(define (apply-procedure p args)
  (match p ((Procedure vars body env)
    (if (not (equal? (length args) (length vars)))
      (error 'apply-procedure
        "procedure arity mismatch between ~a (formal args) and ~a (real args)"
        (length args) (length vars))
      (value-of body (extend-env* vars args env))
    )
  ))
)

; ex 3.19
(define (Letproc->Let procdefs env)
  (if (null? procdefs) (values null null)
    (let-values
      (((vars proc-vals) (Letproc->Let (cdr procdefs) env)))
      (cases ProcDef (car procdefs) (MkProcDef (var params body)
        (let ((p (Proc params body)))
          (values (cons var vars) (cons p proc-vals))
        )
      ))
    )
  )
)

; ex 3.24. factorial
(define factorial-src "
let*
  factrec = proc (rec) proc (n)
    if =(n, 0)
      then 1
      else *(((rec rec) -(n, 1)), n)
  fact = proc (n) ((factrec factrec) n)
in
  (fact 5)
")

; ex 3.25. even/odd
(define even-odd-src "
let*
  evenrec = proc (even-rec, odd-rec) proc (n)
    if zero?(n) then 1 else ((odd-rec even-rec odd-rec) -(n, 1))
  oddrec = proc (even-rec, odd-rec) proc (n)
    if zero?(n) then 0 else ((even-rec even-rec odd-rec) -(n, 1))
  even = (evenrec evenrec oddrec)
  odd  = (oddrec evenrec oddrec)
in
  +((odd 9), (even 10))
")

(define even-odd-letrec-src "
  letrec even(x) = if zero?(x) then 1 else (odd  -(x,1))
         odd (x) = if zero?(x) then 0 else (even -(x,1))
      in list((even 0), (odd 0), (even 1), (odd 1), (even 21), (odd 20))
")

; ex 3.31.

(define (ProcDef->ProcInfo recdef)
  (cases ProcDef recdef
    (MkProcDef (var params body) (ProcInfo var params body))
  )
)

(define (make-rec-env recdefs env)
  (extend-env*-rec (map ProcDef->ProcInfo recdefs) env)
)

(define (eval-letrec recdefs expr env)
  (let ((rec-env (make-rec-env recdefs env)))
    (value-of expr rec-env)
  )
)

((sllgen:make-rep-loop "sllgen> " value-of-program
   (sllgen:make-stream-parser eopl:lex-spec let-syn-spec)))
