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

(define lex-addr cons)
(define lex-addr? (cons-of number? number?))
(define lex-addr-row car)
(define lex-addr-col cdr)
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
  (NList (exprs (list-of NamelessExpr?)))
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

(struct Procedure (body env) #:transparent)

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

(struct variable (name) #:transparent)
(struct normal-var variable () #:transparent)
(struct proc-var   variable (params body env) #:transparent)
(struct letrec-var variable () #:transparent)

(struct static-info (lex-addr var enclosing-env) #:transparent)

(define (same-variable info1 info2)
  (match (cons info1 info2)
    ((cons (static-info addr1 rec1 env1) (static-info addr2 rec2 env2))
     (and (equal? (lex-addr-col addr1) (lex-addr-col addr2)) (eq? env1 env2)))
  )
)

; ex 3.39. ex 3.41. ribcage
(define (empty-senv) null)
(define (extend-senv var senv) (cons (list var) senv))
(define (extend-senv*-normal names senv)
  (extend-senv* (map normal-var names) senv)
)
(define (extend-senv* vars senv) (cons vars senv))
(define (apply-senv senv var)
  (define (apply-senv-impl senv var)
    (define (name-is-var v) (equal? (variable-name v) var))
    (define (increment-row-in-result result)
      (match result ((static-info addr v e)
        (static-info (inc-row addr) v e)
      ))
    )
    (match senv
      ((quote ()) #f)
      ((cons rib senv1)
        (match (index-where rib name-is-var)
          (#f (match (apply-senv-impl senv1 var)
            (#f #f)
            (result (increment-row-in-result result))
          ))
          (found-here (let ((the-var (list-ref rib found-here)))
            (static-info (lex-addr 0 found-here) the-var senv)
          ))
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
    (Var (var) (translate-var var senv))
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
        (translate-of body (extend-senv*-normal vars senv)))
    )

    ; ex 3.40.
    (Letrec (var params proc-body let-body)
      (let ((rec-env (extend-senv (letrec-var var) senv)))
        (NLetrec
          (translate-of proc-body (extend-senv*-normal params rec-env))
          (translate-of let-body rec-env))
      )
    )

    ; ex 3.41.
    (Let (vars vals body)
      (let* ((senv-vars (classify-let-vars vars vals senv))
             (body-senv (extend-senv* senv-vars senv)))
        (NLet (translates vals) (translate-of body body-senv))
      )
    )

    (Proc (params body)
      (NProc (translate-of body (extend-senv*-normal params senv)))
    )

    (Call (proc args) (NCall (translate proc) (translates args)))
  )
)

(define-datatype nameless-env nameless-env?
  (empty-nameless-env)
  (extend-nameless-env* (rib (list-of expval?)) (tail nameless-env?))
)
(define (extend-nameless-env value env)
  (extend-nameless-env* (list value) env)
)
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
(define (translate-var var senv)
  (match (apply-senv senv var) ((static-info addr v se)
    (match v
      ((letrec-var _) (NRecVar addr))
      ((proc-var _ params body _) #:when (share-same-free-vars v senv)
        (translate-of (Proc params body) senv)
      )
      (else (NVar addr)))
  ))
)

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

; ex 3.43.
(define (classify-let-var var val env)
  (cases Expression val
    (Proc (params body) (proc-var var params body env))
    (else (normal-var var))
  )
)
(define (classify-let-vars vars vals env)
  (match vars
    ((quote ()) null)
    ((cons var vars1) (match vals ((cons val vals1)
      (cons
        (classify-let-var var val env)
        (classify-let-vars vars1 vals1 env))
    )))
  )
)
(define (free-variables body params)
  (define (recurse-into . exprs)
    (apply append (map (λ (expr) (free-variables expr params)) exprs))
  )
  (define (subenv-free-variables body1 new-vars)
    (filter
      (compose not (λ (v) (member v params)))
      (free-variables body1 new-vars))
  )
  (cases Expression body
    (Var (var) (if (member var params) null (list var)))
    (Diff (lhs rhs) (recurse-into lhs rhs))
    (Zero? (expr) (recurse-into expr))
    (If (test texpr fexpr) (recurse-into test texpr fexpr))
    (Cond (tests bodies)
      (append (apply recurse-into tests) (apply recurse-into bodies))
    )
    (Cons (head tail) (recurse-into head tail))
    (List (exprs) (apply recurse-into exprs))
    (Unpack (vars val let-body)
      (append (subenv-free-variables let-body vars) (recurse-into val))
    )
    (Letrec (var params1 proc-body let-body)
      (append (subenv-free-variables proc-body (cons var params1))
              (subenv-free-variables let-body (list var)))
    )
    (Let (vars vals body1)
      (append (apply recurse-into vals) (subenv-free-variables body1 vars))
    )
    (Call (f args) (apply recurse-into f args))
    (Proc (params1 body) (subenv-free-variables body params))
    (else null)
  )
)

(define (share-same-free-vars pv senv)
  (match pv ((proc-var _ params body env)
    (let ((free-vars (free-variables body params)))
      (andmap
        (λ (v) (same-variable (apply-senv env v) (apply-senv senv v)))
        free-vars)
    )
  ))
)

; ex 3.44. eliminating dead variable declaration
;
; idea:
; Modify the internal implementation of `translate-of` by adding another
; return value representing the set of "used variables". And translation of any
; kind of `Let` expression makes use of this additional information, eliminating
; each variable which is not used in the "let-body".
;
; Interestingly enough, even if the whole `Let` is eliminated (all variables
; declared in `Let` are unused), a empty rib should still be added to the
; nameless environment during evaluation of this empty `Let`. Otherwise there's
; a chance we break the lexical address of the expression in let-body.
;
; The implementation destroys most of previous exercises and is mostly laborious
; job, so it's omitted... for now.

(define Run (compose run parse))

(define (test-nameless)
  (local-require rackunit)
  (check-equal? 0 (Run "0"))
  (check-equal? 1 (Run "let i = 1 in i") "simple let")
  (check-equal? 2 (Run "let p = proc (n, m) -(n, m) in (p 4 2)"))
  (check-equal? 3 (Run "let i = 1 in if zero?(i) then i else 3"))
  (check-equal? 4 (Run "let i = 0 in if zero?(i) then -(i, -4) else i"))
  (check-equal? 5 (Run "unpack i j k = list(1, -2, -2) in -(-(i, j), k)"))
  (check-equal? 6
    (Run "letrec add(n, m) = if zero?(n) then m else -((add -(n, 1) m), -1)
              in (add 4 2)"))
  (check-equal? 7
    (Run "let i = 1
           in let p = proc(i, j)
                        let i = proc(i) -(i, 1)
                         in (i -(j, 1))
               in let i = 10
                   in (p 5 -(i, 1))"))
  (check-equal? 8
    (Run "let i = -2
           in letrec multtwo(n) = if zero?(n)
                then 0 else -((multtwo -(n, 1)), i)
           in let i = -3 in (multtwo 4)"))
)
(test-nameless)

((sllgen:make-rep-loop "sllgen> " run
    (sllgen:make-stream-parser eopl:lex-spec nameless-syn-spec)))
