#lang racket

(require "../eopl.rkt")

(provide (all-defined-out))

(sllgen:define nameless-syn-spec
  '((Program (Expression) a-program)

    (Expression (number) Num)
    (Expression (identifier) Var)
    (Expression ("-" "(" Expression "," Expression ")") Diff)
    (Expression ("zero?" "(" Expression ")") Zero?)
    (Expression ("if" Expression "then" Expression "else" Expression) If)

    ;; ex 3.38. cond
    (Expression ("cond" (arbno Expression "==>" Expression) "end") Cond)

    ;; ex 3.39. unpack
    (Expression ("cons" "(" Expression "," Expression ")") Cons)
    (Expression ("nil") Nil)

    (Expression ("list" "(" (separated-list Expression ",") ")") List)

    (Expression
      ("unpack" (arbno identifier) "=" Expression "in" Expression)
      Unpack)

    ;; ex 3.40. 
    (Expression
      ("letrec" identifier "(" (separated-list identifier ",") ")" "="
         Expression "in" Expression)
      Letrec)

    ;; ex 3.41. multi-variables let and procedure 
    (Expression
      ("let" (arbno identifier "=" Expression) "in" Expression)
      Let)

    (Expression ("(" Expression (arbno Expression) ")") Call)

    (Expression
      ("proc" "(" (separated-list identifier ",") ")" Expression)
      Proc)
  )
)

(define lex-addr? (cons-of number? number?))
(define (inc-row addr) (cons (add1 (car addr)) (cdr addr)))
(define (inc-col addr) (cons (car addr) (add1 (cdr addr))))

(define-datatype NamelessProgram NamelessProgram?
  (NProgram (expr NamelessExpr?))
)

(define-datatype NamelessExpr NamelessExpr?
  (NNum (n number?))
  (NVar (addr lex-addr?))
  (NDiff (lhs NamelessExpr?) (rhs NamelessExpr?))
  (NZero? (expr NamelessExpr?))
  (NIf (test NamelessExpr?) (texpr NamelessExpr?) (fexpr NamelessExpr?))

  ; ex 3.38.
  (NCond (tests (list-of NamelessExpr?)) (bodies (list-of NamelessExpr?)))

  ; ex 3.39.
  (NCons (head NamelessExpr?) (tail NamelessExpr?))
  (NNil)
  (NList (exprs NamelessExpr?))
  (NUnpack (lsexpr NamelessExpr?) (body NamelessExpr?))

  ; ex 3.40.
  (NRecVar (addr lex-addr?))
  (NLetrec (proc-body NamelessExpr?) (let-body NamelessExpr?))

  ; ex 3.41.
  (NLet (vals (list-of NamelessExpr?)) (body NamelessExpr?))
  (NProc (body NamelessExpr?))
  (NCall (proc NamelessExpr?) (args (list-of NamelessExpr?)))
)

(sllgen:make-define-datatypes eopl:lex-spec nameless-syn-spec)

(define parse (sllgen:make-string-parser eopl:lex-spec nameless-syn-spec))

(struct Procedure (body env))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc Procedure?))

  ; ex 3.39.
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
(define (expval->list val)
  (cases expval val
    (list-val (l) l)
    (else (report-expval-extractor-error 'list val))
  )
)
(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else (report-expval-extractor-error 'proc val))
  )
)
(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (list-val (l) l)
    (proc-val (p) p)
  )
)

(struct variable (value))
(struct normal-var variable ())
(struct letrec-var variable ())

(define (map-variable f var)
  (match var
    ((normal-var val) (normal-var (f val)))
    ((letrec-var val) (letrec-var (f val)))
  )
)

; ex 3.39. ex 3.41. ribcage
(define (empty-senv) null)
(define (extend-senv var senv) (cons (list (normal-var var)) senv))
(define (extend-senv* vars senv) (cons (map normal-var vars) senv))
(define (extend-senv-rec var senv)
  (cons (list (letrec-var var)) senv)
)
(define (apply-senv senv var)
  (define (apply-senv-impl senv var)
    (define (name-is-var v) (equal? (variable-value v) var))
    (match senv
      ((quote ()) #f)
      ((cons rib senv1)
        (match (index-where rib name-is-var)
          (#f (match (apply-senv-impl senv1 var)
            (#f #f)
            (v (map-variable inc-row v))
          ))
          (found-here
            (map-variable
              (λ (name) (cons 0 found-here)) (list-ref rib found-here)))
        )
      )
    )
  )
  (let ((result (apply-senv-impl senv var)))
    (if result result
      (error 'apply-senv "variable ~a not found in ~a" var senv)
    )
  )
)

(define init-senv empty-senv)

(define (translate-of-program p)
  (cases Program p
    (a-program (expr) (NProgram (translate-of expr (init-senv))))
  )
)

(define (eval-nameless-program program)
  (cases NamelessProgram program
    (NProgram (expr) (eval-nameless expr (empty-nameless-env)))
  )
)

(define run
  (compose expval->val eval-nameless-program translate-of-program))

(define (translate-of expr senv)
  (define (translate e) (translate-of e senv))
  (define (translates exprs) (map translate exprs))
  (cases Expression expr
    (Num (n) (NNum n))
    (Var (var)
      (let* ((var-addr (apply-senv senv var))
             (addr (variable-value var-addr)))
        (if (normal-var? var-addr) (NVar addr) (NRecVar addr))
      )
    )
    (Diff (lhs rhs) (NDiff (translate lhs) (translate rhs)))
    (Zero? (expr) (NZero? (translate expr)))

    (If (test texpr fexpr)
      (NIf (translate test) (translate texpr) (translate fexpr))
    )

    ; ex 3.38.
    (Cond (tests bodies) (NCond (translates tests) (translates bodies)))

    ; ex 3.39.
    (Cons (head tail) (NCons (translate head) (translate tail)))
    (Nil () NNil)
    (List (exprs) (NList (translates exprs)))

    (Unpack (vars lexpr body)
      (NUnpack (translate lexpr)
        (translate-of body (extend-senv* vars senv)))
    )

    ; ex 3.40.
    (Letrec (var params proc-body let-body)
      (let ((rec-env (extend-senv-rec var senv)))
        (NLetrec
          (translate-of proc-body (extend-senv* params rec-env))
          (translate-of let-body rec-env))
      )
    )

    ; ex 3.41.
    (Let (vars vals body)
      (NLet
        (translates vals) (translate-of body (extend-senv* vars senv)))
    )

    (Proc (params body)
      (NProc (translate-of body (extend-senv* params senv)))
    )

    (Call (proc args) (NCall (translate proc) (translates args)))
  )
)

(define-datatype nameless-env nameless-env?
  (empty-nameless-env)
  (extend-nameless-env* (rib (list-of expval?)) (tail nameless-env?))
)
(define (extend-nameless-env value env) (extend-nameless-env* (list value) env))
(define (apply-nameless-env env addr)
  (define (apply-nameless-rib rib col)
    (if (>= col (length rib)) #f (list-ref rib col))
  )
  (define (apply-nameless-env-impl env addr)
    (cases nameless-env env
      (empty-nameless-env () #f)
      (extend-nameless-env* (vals tail)
        (let ((row (car addr)) (col (cdr addr)))
          (if (equal? row 0)
            (apply-nameless-rib vals col)
            (apply-nameless-env-impl tail (cons (- row 1) col))
          )
        )
      )
    ) ; cases
  )
  (match (apply-nameless-env-impl env addr)
    (#f (error 'apply-nameless-env "invalid address ~a for ~a" addr env))
    (result result)
  )
)

(define (eval-nameless expr env)
  (define (eval e) (eval-nameless e env))
  (cases NamelessExpr expr
    (NNum (n) (num-val n))
    (NVar (addr) (apply-nameless-env env addr))
    (NDiff (lhs rhs)
      (num-val (- (expval->num (eval lhs)) (expval->num (eval rhs))))
    )
    (NZero? (e) (bool-val (zero? (expval->num (eval e)))))
    (NIf (test texpr fexpr)
      (if (expval->bool (eval test)) (eval texpr) (eval fexpr))
    )

    ; ex 3.38.
    (NCond (tests bodies) (eval (NCond->NIf tests bodies)))

    ; ex 3.39.
    (NNil () (list-val null))
    (NCons (head tail)
      (list-val (cons (eval head) (expval->list (eval tail))))
    )
    (NList (exprs) (list-val (map eval exprs)))

    (NUnpack (expr body)
      (eval-nameless
        body (extend-nameless-env* (expval->list (eval expr)) env))
    )

    ; ex 3.40.
    (NRecVar (addr)
      (proc-val
        (rec-proc->proc (expval->proc (apply-nameless-env env addr))))
    )
    (NLetrec (proc-body let-body)
      (eval-nameless
        let-body (extend-nameless-env (proc-val (Procedure proc-body env)) env))
    )

    ; ex 3.41.
    (NLet (exprs body)
      (eval-nameless body (extend-nameless-env* (map eval exprs) env))
    )

    (NProc (body) (proc-val (Procedure body env)))
    (NCall (proc args)
      (apply-procedure (expval->proc (eval proc)) (map eval args))
    )
  )
)

; ex 3.38.
(define (NCond->NIf tests bodies)
  (if (null? tests) (error 'NCond->NIf "non-exhausted-matches")
    (let ((test   (car tests)) (body    (car bodies))
          (tests1 (cdr tests)) (bodies1 (cdr bodies)))
      (NIf test body (NCond tests1 bodies1))
    )
  )
)

; ex 3.40.
(define (rec-proc->proc p)
  (match p ((Procedure body env)
    (Procedure body (extend-nameless-env (proc-val p) env))
  ))
)

; ex 3.41.
(define (apply-procedure proc args)
  (match proc ((Procedure body env)
    (eval-nameless body (extend-nameless-env* args env))
  ))
)

((sllgen:make-rep-loop "sllgen> " run
    (sllgen:make-stream-parser eopl:lex-spec nameless-syn-spec)))
