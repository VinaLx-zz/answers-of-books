#lang racket

(require "cps-in.rkt")
(require "cps-out.rkt")
(require "../eopl.rkt")

(define (with-gensym base cont)
  (let ((sym (gensym base))) (cont sym))
)
(define (make-cps-cont f)
  (with-gensym 'r (λ (r)
    (SProc (list r) (f (SVar r)))
  ))
)

(define (tailform-of-program p)
  (cases Program p
    (a-program (expr) (tf-program (tailform-of-expr expr)))
  )
)
(define (tailform-of-expr expr)
  (cps-of-expr expr #f)
)

(define ((send-to-cont k) simple-expr)
  (cases SimpleExpr k
    (SProc (params body) (match params ((list r)
      ; ex 6.22.
      ; translate `(Call Proc(r) body param)` to `let r = param in body`
      ;
      ; (TfLet (list r) (list simple-expr) body)
      
      ; ex 6.26. substitute the result variable with the simple-expr
      (inline-var-binding body r simple-expr)
    )))
    (else (TfCall k (list simple-expr)))
  )
)

(define cps-end-cont (make-cps-cont (λ (rvar) (TfSimple rvar))))

(define (cps-of-expr input-expr k)
  (define apply-cont
    (if k (send-to-cont k) TfSimple)
  )
  (define (entity-of k) (if k k cps-end-cont))
  (cases Expression input-expr
    ; ex 6.25. arbitrary amount of binding in `let`
    (Let (vars vals body) (cps-of-let vars vals body k))

    (Letrec (defs body)
      (TfLetrec (map cps-of-procdef defs) (cps-of-expr body k))
    )

    (If (test iftrue iffalse) (cps-of-if test iftrue iffalse k))

    (Call (proc args)
      (extract-simple proc (λ (sproc)
        (extract-simples args (λ (sargs)
          (TfCall sproc (append sargs (list (entity-of k))))
        ))
      ))
    )
    (else (extract-simple input-expr apply-cont))
  )
)

; ex 6.30.
; Accidentally my implementation coincides with the implementation choice of
; `cps-of-exp/ctx` in ex 6.30. The idea is almost identical, but differs from
; the concrete implementation.
(define (extract-simple input-expr cont (suggest-var-name #f))
  (cases Expression input-expr
    (Num (n) (cont (SNum n)))
    (Var (v) (cont (SVar v)))
    (Zero? (expr)
      (extract-simple expr (λ (r)
        (cont (SZero? r))
      ))
    )
    (Diff (lhs rhs)
      (extract-simple lhs (λ (l)
        (extract-simple rhs (λ (r)
          (cont (SDiff l r))
        ))
      ))
    )
    (Sum (exprs)
      (extract-simples exprs (λ (sexprs)
        (cont (SSum sexprs))
      ))
    )
    (Proc (vars body)
      (define cps-proc (with-gensym 'cont (λ (contvar)
        (SProc (append vars (list contvar))
          (cps-of-expr body (SVar contvar)))
      )))
      (cont cps-proc)
    )
    (else
      (let ((rvar (if suggest-var-name suggest-var-name (gensym 'r))))
        (cps-of-expr input-expr (SProc (list rvar) (cont (SVar rvar))))
      )
    )
  )
)

(define (extract-simples exprs cont)
  (match exprs
    ((quote ()) (cont null))
    ((cons expr exprs1)
      (extract-simple expr (λ (r)
        (extract-simples exprs1 (λ (rs) (cont (cons r rs))))
      ))
    ) ; cons
  ) ; match
)

(define (cps-of-procdef def)
  (cases ProcDef def
    (MkProcDef (name vars body)
      (with-gensym 'cont (λ (contvar)
        (MkTfProcDef
          name (append vars (list contvar))
          (cps-of-expr body (SVar contvar)))
      ))
    )
  )
)

; ex 6.23. eliminate the duplicate of continuation in 'if'
(define (cps-of-if test iftrue iffalse k)
  (extract-simple test (λ (stest)
    (define (if-with-cont k)
      (TfIf stest (cps-of-expr iftrue k) (cps-of-expr iffalse k))
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
      (SSum (exprs) (SSum (map inline-simple exprs)))
      (SZero? (expr) (SZero? (inline-simple expr)))
      (SProc (params body) (inline-tailform body))
    )
  )
  (define (inline-tailform input-expr)
    (inline-var-binding input-expr ident sexpr)
  )
  (cases TailFormExpr input-expr
    (TfSimple (simple) (TfSimple (inline-simple simple)))
    (TfLet (vars simples tail)
      (TfLet vars simples (inline-tailform tail))
    )
    (TfIf (test iftrue iffalse)
      (TfIf test
        (inline-tailform iftrue) (inline-tailform iffalse))
    )
    (TfCall (proc args) (TfCall proc (map inline-simple args)))
    (TfLetrec (defs body)
      (TfLetrec defs (inline-tailform body))
    )
  )
)


; ex 6.27. eliminate the useless assignment from `let`
(define (cps-of-let vars vals body k)
  (define (pick-non-simple-vars vars vals letk)
    (match* (vars vals)
      (((quote ()) (quote())) (letk null null))
      (((cons var vars1) (cons val vals1))
        (extract-simple val (λ (sval)
          (pick-non-simple-vars vars1 vals1 (λ (svars svals)
            (cases SimpleExpr sval
              (SVar (v) (letk svars svals))
              (else (letk (cons var svars) (cons sval svals)))
            )
          ))
        ) var) ; extract simple with suggest variable name 'var'
      )
    )
  )
  (pick-non-simple-vars vars vals (λ (svars svals)
    (define let-body (cps-of-expr body k))
    (if (null? svars) let-body
      (TfLet svars svals let-body)
    )
  ))
)


; (require racket/trace)
; (trace cps-of-expr)

(define (print-cps p)
  (pretty-print (tailform-of-program p))
)

((sllgen:make-rep-loop "cps-in> " print-cps
   (sllgen:make-stream-parser eopl:lex-spec cps-in-syntax)))
