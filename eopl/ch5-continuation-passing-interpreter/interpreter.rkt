#lang racket

(require "data.rkt")
(require "../eopl.rkt")
(require (submod "../ch4-state/store.rkt" global-mutable))
(require "cont.rkt")
(require "thread/scheduler.rkt")
(require "thread/mutex.rkt")

(sllgen:define syntax-spec
  '((Program (Expression) a-program)

    (Expression (number) Num)
    (Expression (identifier) Var)
    (Expression ("-" "(" Expression "," Expression ")") Diff)
    (Expression ("zero?" "(" Expression ")") Zero?)
    (Expression ("not" "(" Expression ")") Not)
    (Expression ("if" Expression "then" Expression "else" Expression) If)
    (Expression ("print" "(" Expression ")") Print)

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

    ; exceptions
    (Expression
      ("try" Expression "catch" "(" identifier "," identifier ")" Expression)
      Try)
    (Expression ("raise" Expression) Raise)

    ; ex 5.38. division
    (Expression ("/" "(" Expression "," Expression ")") Div)

    ; ex 5.39. raise and resume
    (Expression ("raise_" Expression) Raise_)

    ; ex 5.40. ex 5.42.
    (Expression ("throw" Expression "to" Expression) Throw)

    ; ex 5.41.
    (Expression ("letcc" identifier "in" Expression) Letcc)

    ; ex 5.44. relation between callcc/letcc/throw
    (Expression ("callcc") CallCC)

    (Expression ("letcc_" identifier "in" Expression) Letcc_)
    (Expression ("throw_" Expression "to" Expression) Throw_)

    ; thread
    (Expression ("spawn" "(" Expression ")") Spawn)

    (Expression ("mutex" "(" ")") Mutex)
    (Expression ("lock" "(" Expression ")") Lock)
    (Expression ("unlock" "(" Expression ")") Unlock)
  )
)

(sllgen:make-define-datatypes eopl:lex-spec syntax-spec)
(define parse (sllgen:make-string-parser eopl:lex-spec syntax-spec))

(define (value-of-program pgm)
  (cases Program pgm
    (a-program (expr)
      (initialize-store!)
      (initialize-scheduler! 1)
      (let ((bounce (value-of/k expr (empty-env) #f end-main-thread)))
        (expval->val (trampoline bounce))
      )
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

; ex 5.35. ex 5.36. using two continuations to implement exception
(define (value-of/k expr env handler cont)
  (define (return v) (apply-cont cont v))
  (cases Expression expr
    (Num (n) (return (num-val n)))
    (Var (var) (return (deref (apply-env env var))))
    (Proc (params body)
      (return (make-procedure-val params body env))
    )
    (Letrec (procdef procdefs body)
      (eval-letrec/k (cons procdef procdefs) body env handler cont)
    )
    (Not (expr)
      (value-of/k expr env handler (λ (val)
        (return (bool-val (not (expval->bool val))))
      ))
    )
    (Zero? (expr)
      (value-of/k expr env handler (λ (val)
        (return (bool-val (zero? (expval->num val))))
      ))
    )
    (Print (expr)
      (value-of/k expr env handler (λ (val)
        (printf "~a\n" (expval->val val))
        (apply-cont cont (void-val))
      ))
    )
    (If (test texpr fexpr)
      (value-of/k test env handler (λ (val)
        (if (expval->bool val)
          (value-of/k texpr env handler cont)
          (value-of/k fexpr env handler cont))
      ))
    )
    (Diff (lhs rhs)
      (value-of/k lhs env handler (λ (v1)
        (value-of/k rhs env handler (λ (v2)
          (return (num-val (- (expval->num v1) (expval->num v2))))
        ))
      ))
    )
    ; ex 5.5. ex 5.6.
    (Nil () (return (list-val null)))
    (Cons (head tail)
      (value-of/k head env handler (λ (h)
        (value-of/k tail env handler (λ (t)
          (return (list-val (cons h (expval->list t))))
        ))
      ))
    )
    (List (exprs)
      (values-of/k exprs env handler (λ (vals) (return (list-val vals))))
    )

    ; ex 5.7.
    (Let (vars exprs body)
      (values-of/k exprs env handler (λ (vals)
        (let ((new-env (extend-env* vars (map newref vals) env)))
          (value-of/k body new-env handler cont)
        )
      ))
    )
    
    ; ex 5.8.
    (Call (operator operands)
      (value-of/k operator env handler (λ (opval)
        (cases expval opval
          (proc-val (proc) (apply-procedure/k proc operands env handler cont))
          ; ex 5.43. support procedure invoking syntax for continuation
          (cont-val (c)
            (if (equal? (length operands) 1)
              (value-of/k
                (car operands) env handler (λ (val) (apply-cont c val)))
              (raise-wrong-arguments-exception handler 1 cont)
            )
          )
          (else (report-expval-extractor-error 'proc-or-cont opval))
        )
      ))
    )

    ; ex 5.9.
    ; ex 5.10. Not keeping environment in continuation
    (Set (ident expr)
      (let ((ref (apply-env env ident)))
        (value-of/k expr env handler (λ (val)
          (setref! ref val)
          (return (void-val))
        ))
      )
    )

    ; ex 5.11.
    (Begin_ (exprs)
      (values-of/k exprs env handler (λ (vals) (return (last vals))))
    )

    ; exceptions
    (Try (tried kvar evar catch-expr)
      (let ((new-handler
             (exception-handler kvar evar catch-expr env cont handler)))
        (value-of/k tried env new-handler cont)
      )
    )
    (Raise (expr)
      (value-of/k expr env handler (λ (err) (apply-handler handler err cont)))
    )

    ; ex 5.38. division
    (Div (lhs rhs)
      (value-of/k lhs env handler (λ (lval)
        (value-of/k rhs env handler (λ (rval)
          (if (zero? (expval->num rval)) (apply-handler handler lval cont)
            (return (num-val (quotient (expval->num lval) (expval->num rval))))
          )
        ))
      ))
    )

    ; ex 5.39.
    (Raise_ (expr)
      (value-of/k expr env handler
        (λ (err) (apply-handler-with-cont handler err cont))
      )
    )

    ; ex 5.39. ex 5.42.
    (Throw (vexpr cexpr)
      (value-of/k cexpr env handler (λ (cval)
        (define c (expval->cont cval))
        (value-of/k vexpr env handler (λ (val) (apply-cont c val)))
      ))
    )

    ; ex 5.41.
    (Letcc (kvar body)
      (let ((new-env (extend-env kvar (newref (cont-val cont)) env)))
        (value-of/k body new-env handler cont)
      )
    )

    ; ex 5.44.
    (CallCC () (value-of/k
      (Proc '(callcc-proc)
        (Letcc 'callcc-cont
          (Call (Var 'callcc-proc) (list
            (Proc '(callcc-return-var)
              (Throw (Var 'callcc-return-var) (Var 'callcc-cont)))
      )))) env handler cont
    ))

    (Letcc_ (kvar body) (value-of/k
      (Call (CallCC) (list (Proc (list kvar) body)))
      env handler cont
    ))

    (Throw_ (vexpr kexpr) (value-of/k
      (Call kexpr (list vexpr))
      env handler cont
    ))

    ; thread

    (Spawn (expr)
      (value-of/k expr env handler (λ (p)
        (add-to-ready-queue! (λ ()
          (apply-procedure/k (expval->proc p) null env #f end-subthread)))
        (apply-cont cont (void-val))
      ))
    )

    (Mutex () (apply-cont cont (mutex-val (new-mutex))))

    (Lock (mexpr)
      (value-of/k mexpr env handler (λ (m)
        (mutex-lock! (expval->mutex m)
          (λ () (apply-cont cont (void-val)))
        )
      ))
    )
    (Unlock (mexpr) 
      (value-of/k mexpr env handler (λ (m)
        (mutex-unlock! (expval->mutex m))
        (apply-cont cont (void-val))
      ))
    )
  )
)

(define (eval-letrec/k recdefs expr env handler cont)
  (define (ProcDef->ProcInfo recdef)
    (cases ProcDef recdef
      (MkProcDef (var params body) (ProcInfo var params body))
    )
  )
  (define (make-rec-env recdefs env)
    (extend-env*-rec (map ProcDef->ProcInfo recdefs) env)
  )
  (let ((rec-env (make-rec-env recdefs env)))
    (value-of/k expr rec-env handler cont)
  )
)

(define (raise-wrong-arguments-exception handler right-nargs cont)
  (apply-handler handler (num-val right-nargs) cont)
)

; trampolined apply-procedure/k
(define (apply-procedure/k p args env handler cont) (λ ()
  (match p ((Procedure params body penv)
    (if (not (equal? (length args) (length params)))
      ; ex 5.37.
      ; raise exception when procedure is applied with wrong number of arguments
      (raise-wrong-arguments-exception handler (length params) cont)
      (values-of/k args env handler (λ (vals)
        (define refs (map newref vals))
        (value-of/k body (extend-env* params refs penv) handler cont)
      ))
    )
  ))
))

; helper for evaluating multiple values
(define (values-of/k exprs env handler cont)
  (define (values-of/k-impl acc exprs)
    (match exprs
      ((quote ()) (apply-cont cont (reverse acc)))
      ((cons expr exprs1)
        (value-of/k expr env handler (λ (v)
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

; exception
; ex 5.35. ex 5.36.
(struct exception-handler
  (resume-var catch-var catch-expr env cont next-handler)
)
(define (apply-handler handler err resume-cont)
  (match handler
    ((exception-handler resume-var catch-var catch-expr env cont next-handler)
      (let ((catch-env
             (extend-env*
               (list resume-var catch-var)
               (list (newref (cont-val resume-cont)) (newref err)) env)))
        (value-of/k catch-expr catch-env next-handler cont)
      )
    )
    (#f
      (printf "uncaught cps exception: ~a\n" (expval->val err))
      (void-val)
    )
  )
)

; ex 5.39. resume execution from raise expression
(define (apply-handler-with-cont handler err cont)
  (match handler
    ((exception-handler kv cv ce env _ h)
      (apply-handler (exception-handler kv cv ce env cont h) err cont)
    )
    (else (apply-handler handler err cont))
  )
)

(define run-source (compose value-of-program parse))

(define thread-example "
let buffer = 0
in let producer = proc ()
  letrec wait(k) =
    if zero?(k)
    then set buffer = 42
    else
      begin print(-(k, -200))
          ; (wait -(k, 1))
      end
  in (wait 5)
in let consumer = proc ()
  letrec wait(k) =
    if zero?(buffer)
    then
      begin print(-(k, -100))
          ; (wait -(k, -1))
      end
    else buffer
in (wait 0)
in
begin spawn(producer)
    ; print(300)
    ; (consumer)
end
")

(define mutex-example "
let x = 0 in
let mut = mutex() in
let incrx = proc () begin
  lock(mut);
  set x = -(x, -1);
  unlock(mut);
  print(x)
end in
begin spawn(incrx) ; spawn(incrx) ; spawn(incrx)
    ; spawn(incrx) ; spawn(incrx) ; spawn(incrx)
end
")

(provide (all-defined-out))

; ((sllgen:make-rep-loop "sllgen> " value-of-program
   ; (sllgen:make-stream-parser eopl:lex-spec syntax-spec)))
