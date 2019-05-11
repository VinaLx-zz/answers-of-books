#lang racket

(require "cps-in.rkt")
(require "cps-out.rkt")
(require "../eopl.rkt")

(define (with-gensym base cont)
  (let ((sym (gensym base))) (cont sym))
)
(define (make-cps-cont f #:param-name (param-name #f))
  (define var (if param-name param-name (gensym 'r)))
  (SProc (list var) (f (SVar var)))
)

(define (tailform-of-program p)
  (cases Program p
    (a-program (expr) (tf-program (tailform-of-expr expr)))
  )
)
(define cps-end-cont (make-cps-cont (λ (rvar) (TfSimple rvar))))
(define uncaught-exception-cont
  (make-cps-cont #:param-name (gensym 'err) (λ (rvar)
    (TfPrint (SNum 10101010) (TfSimple rvar))
  ))
)

(define (tailform-of-expr expr)
  (cps-of-expr expr cps-end-cont uncaught-exception-cont)
)

(define ((send-to-cont k) simple-expr)
  (cases SimpleExpr k
    (SProc (params body) (match params ((list r)
    ; ex 6.22.
    ; translate `(Call Proc(r) body param)` to `let r = param in body`
    ;
      (TfLet (list r) (list simple-expr) body)

    ; ex 6.26. substitute the result variable with the simple-expr
    ; (inline-var-binding body r simple-expr)
    )))
    (else (TfCall k (list simple-expr)))
  )
)

(define (cps-of-expr input-expr k failk)
  (define success (send-to-cont k))
  (define fail (send-to-cont failk))

  (cases Expression input-expr
    ; ex 6.25. arbitrary amount of binding in `let`
    (Let (vars vals body) (cps-of-let vars vals body k failk))

    (Letrec (defs body)
      (TfLetrec (map cps-of-procdef defs) (cps-of-expr body k failk))
    )

    (If (test iftrue iffalse) (cps-of-if test iftrue iffalse k failk))

    (Call (proc args)
      (extract-simple proc failk (λ (sproc)
        (extract-simples args failk (λ (sargs)
          (newrefs sargs
            (λ (refs) (TfCall sproc (append refs (list k failk))))
          )
        ))
      ))
    )

    (Print (expr)
      (extract-simple expr failk (λ (sexpr)
        (TfPrint sexpr (success (SNum 0)))
      ))
    )

    ; ex 6.36
    (Begin_ (exprs)
      (extract-simples exprs failk (λ (sexprs)
        (success (last sexprs))
      ))
    )

    ; ex 6.37. implicit reference
    (Set (ident expr)
      (extract-simple expr failk (λ (sexpr)
        (TfSetRef (SVar ident) sexpr (success (SNum 0)))
      ))
    )

    (Var (v) (TfDeref (SVar v) k))

    ; ex 6.39.
    (LetCC (ccvar expr)
      (with-newref k (λ (kref)
        (TfLet (list ccvar) (list kref) (cps-of-expr expr k failk))
      ))
    )

    (Throw (vexpr contexpr)
      (extract-simple contexpr failk (λ (scont)
        (extract-simple vexpr failk (λ (sval)
          ((send-to-cont scont) sval)
        ))
      ))
    )

    ; ex 6.40.
    (TryCatch (try-expr evar catch-expr)
      (define catch-tail (cps-of-expr catch-expr k failk))
      (cps-of-expr try-expr k
        (make-cps-cont #:param-name 'err-val (λ (err-val)
          (with-newref err-val (λ (rref)
            (TfLet (list evar) (list rref) catch-tail)
          ))
        ))
      )
    )

    (Raise (expr)
      (extract-simple expr failk (λ (sexpr) (fail sexpr)))
    )


    (else (extract-simple input-expr failk success))
  )
)

; ex 6.30.
; Accidentally my implementation coincides with the implementation choice of
; `cps-of-exp/ctx` in ex 6.30. The idea is almost identical, but differs from
; the concrete implementation.
(define (extract-simple input-expr failk cont
           #:new-cont-param (new-cont-param #f))
  (define (make-cont f) (make-cps-cont #:param-name new-cont-param f))
  (cases Expression input-expr
    (Num (n) (cont (SNum n)))
    (Zero? (expr)
      (extract-simple expr failk (λ (r)
        (cont (SZero? r))
      ))
    )
    (Diff (lhs rhs)
      (extract-simple lhs failk (λ (l)
        (extract-simple rhs failk (λ (r)
          (cont (SDiff l r))
        ))
      ))
    )
    (Sum (exprs)
      (extract-simples exprs failk (λ (sexprs)
        (cont (SSum sexprs))
      ))
    )
    (Proc (params body) (cont (cps-of-proc-decl params body SProc)))

    (else
      (cps-of-expr input-expr (make-cont (λ (rvar) (cont rvar))) failk)
    )
  )
)

(define (extract-simples exprs failk cont)
  (match exprs
    ((quote ()) (cont null))
    ((cons expr exprs1)
      (extract-simple expr failk (λ (r)
        (extract-simples exprs1 failk (λ (rs) (cont (cons r rs))))
      ))
    ) ; cons
  ) ; match
)

(define (cps-of-proc-decl params body cont)
  (with-gensym 'cont (λ (contvar)
    (with-gensym 'fail (λ (failvar)
      (define new-params (append params (list contvar failvar)))
      (define body-cps (cps-of-expr body (SVar contvar) (SVar failvar)))
      (cont new-params body-cps)
    ))
  ))
)

(define (cps-of-procdef def)
  (cases ProcDef def (MkProcDef (name params body)
    (cps-of-proc-decl params body (λ (params body)
      (MkTfProcDef name params body)
    ))
  ))
)

; ex 6.23. eliminate the duplicate of continuation in 'if'
(define (cps-of-if test iftrue iffalse k failk)
  (extract-simple test failk (λ (stest)
    (define (if-with-cont k)
      (TfIf stest
        (cps-of-expr iftrue k failk) (cps-of-expr iffalse k failk))
    )
    (cases SimpleExpr k
      (SVar (v) (if-with-cont k))
      (else (with-gensym 'cont (λ (contvar)
        (TfLet (list contvar) (list k) (if-with-cont (SVar contvar)))
      )))
    )
  ))
)

; ex 6.26. manually inlining the let definition in `send-to-cont`
(define (inline-var-binding input-expr ident sexpr)
  (define (inline-simple input-expr)
    (cases SimpleExpr input-expr
      (SVar (v) (if (equal? v ident) sexpr input-expr))
      (SNum (n) input-expr)
      (SDiff (lhs rhs) (SDiff (inline-simple lhs) (inline-simple rhs)))
      (SSum (exprs) (SSum (inline-simples exprs)))
      (SZero? (expr) (SZero? (inline-simple expr)))
      (SProc (params body) (SProc params (inline-tailform body)))
    )
  )
  (define (inline-simples exprs)
    (map inline-simple exprs)
  )
  (define (inline-tailform input-expr)
    (inline-var-binding input-expr ident sexpr)
  )
  (cases TailFormExpr input-expr
    (TfSimple (simple) (TfSimple (inline-simple simple)))
    (TfLet (vars simples tail)
      (TfLet vars (inline-simples simples) (inline-tailform tail))
    )
    (TfIf (test iftrue iffalse)
      (TfIf (inline-simple test)
        (inline-tailform iftrue) (inline-tailform iffalse))
    )
    (TfCall (proc args)
      (TfCall (inline-simple proc) (inline-simples args))
    )
    (TfLetrec (defs body)
      (TfLetrec defs (inline-tailform body))
    )
    (TfPrint (simple tail)
      (TfPrint (inline-simple simple) (inline-tailform tail))
    )
    (TfNewRef (sexpr scont)
      (TfNewRef (inline-simple sexpr) (inline-simple scont))
    )
    (TfDeref (sref scont)
      (TfDeref (inline-simple sref) (inline-simple scont))
    )
    (TfSetRef (sref sexpr tail)
      (TfSetRef
        (inline-simple sref) (inline-simple sexpr) (inline-tailform tail))
    )
  )
)

; ex 6.27. eliminate the useless assignment from `let`.
; Unfortunately this optimization isn't compatible with transforming implicit
; reference language to tail-formed explicit reference language, since passing
; variable through continuation doesn't (and shouldn't) create additional
; reference. So the attempt to treat the parameter of continuation as a
; reference would fail if we apply this optimization.
; So we can only do it in the original way by creating a reference for each
; simple expression extracted and bind to the 'let' variable manually.
(define (cps-of-let vars vals body k failk)
  (define (sexpr-is-var expr var)
    (cases SimpleExpr expr
      (SVar (v) (equal? v var))
      (else false)
    )
  )
  (match* (vars vals)
    (((quote ()) (quote ())) (cps-of-expr body k failk))
    (((cons var vars1) (cons val vals1))
      (define let-tail (cps-of-let vars1 vals1 body k failk))
      (extract-simple val failk #:new-cont-param var (λ (sval)
        (if (sexpr-is-var sval var) let-tail
          (TfNewRef sval (make-cps-cont #:param-name var (λ (rvar) let-tail)))
        )
      ))
    )
  )
)

; ex 6.37.
(define (newrefs simples cont)
  (match simples
    ((quote ()) (cont null))
    ((cons simple simples1)
      (define refk (make-cps-cont #:param-name (gensym 'ref) (λ (ref) 
        (newrefs simples1 (λ (refs) (cont (cons ref refs))))
      )))
      (TfNewRef simple refk)
    )
  )
)

(define (with-newref simple cont)
  (TfNewRef simple
    (make-cps-cont #:param-name (gensym 'ref)
      (λ (refvar) (cont refvar))
    )
  )
)


; (require racket/trace)
; (trace cps-of-expr)

(define (print-cps p)
  (pretty-print (tailform-of-program p))
)

(define (transform-and-eval cps-in-program)
  (define cps-out-program (tailform-of-program cps-in-program))
  (pretty-print cps-out-program)
  (eval-cps-out cps-out-program)
)

((sllgen:make-rep-loop "cps-in> " transform-and-eval 
   (sllgen:make-stream-parser eopl:lex-spec cps-in-syntax)))
