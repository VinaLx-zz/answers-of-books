#lang racket

(require "../ch2-data-abstraction/environment.rkt")
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
  )
)

(sllgen:make-define-datatypes eopl:lex-spec let-syn-spec)
(define parse (sllgen:make-stream-parser eopl:lex-spec let-syn-spec))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))

  ; ex 3.9.
  (list-val (l list?))
)

(define (report-expval-extractor-error type value)
  (error 'type-error "expect value: ~a to be type: ~a" value type)
)
(define (expval->num val)
  (cases expval val
    (num-val (num) num)
    (else (report-expval-extractor-error 'num val))
  )
)
(define (expval->bool val)
  (cases expval val
    (bool-val (bool) bool)
    (else (report-expval-extractor-error 'bool val))
  )
)

; ex 3.9.
(define (expval->list val)
  (cases expval val
    (list-val (l) l)
    (else (report-expval-extractor-error 'list val))
  )
)
(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (list-val (l) l)
  )
)

(define (init-env)
  (extend-env 'i (num-val 1)
    (extend-env 'v (num-val 5)
      (extend-env 'x (num-val 10)
         (empty-env))))
)

(define (value-of-program pgm)
  (cases Program pgm
    (a-program (expr) (value-of expr (init-env)))
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
    (Cond (tests bodies) (eval-cond tests bodies env))

    ; ex 3.15
    (Print (expr) (begin
      (display (expval->val (value-of expr env)))
      (num-val 1)
    ))

    ; ex 3.16
    (Let (vars vals body)
      (let
        ((new-env
          (extend-env* vars (map (λ (val) (value-of val env)) vals) env)))
        (value-of body new-env)
      )
    )

    ; ex 3.17
    (Let* (vars vals body)
      (let
        ((new-env
          (foldl (λ (vv acc)
              (extend-env (car vv) (value-of (cdr vv) acc) acc))
            env (zip vars vals))
        ))
        (value-of body new-env)
      )
    )

    ; ex 3.18
    (Unpack (idents val body)
      (let ((vals (expval->list (value-of val env))))
        (if (not (equal? (length idents) (length vals)))
          (error 'unpack "arity mismatch of identifiers and values")
          (value-of body (extend-env* idents vals env))
        )
      )
    )
  ) ; cases
) ; value-of

(define (zip l1 l2)
  (if (or (null? l1) (null? l2)) null
    (cons (cons (car l1) (car l2)) (zip (cdr l1) (cdr l2)))
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
(define (eval-cond tests bodies env)
  (if (null? tests) (error 'eval-cond "non-exhausted-matches")
    (if (expval->bool (value-of (car tests) env))
      (value-of (car bodies) env)
      (eval-cond (cdr tests) (cdr bodies) env)
    )
  )
)

((sllgen:make-rep-loop "> " value-of-program parse))
