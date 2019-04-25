#lang racket

;; mostly copied from "ch3-expression/procedure.rkt"

(require "../../eopl.rkt")
(require "../store.rkt")

(provide (all-defined-out))

(struct Procedure (vars body env) #:transparent)

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc Procedure?))

  ;; explicit-refs
  (ref-val (ref reference?))
  (void-val)
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
(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else (report-expval-extractor-error 'proc val))
  )
)
(define (expval->ref val)
  (cases expval val
    (ref-val (ref) ref)
    (else (report-expval-extractor-error 'ref val))
  )
)

(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (ref-val (r) r)
    (void-val () (void))
  )
)

(define (make-procedure-val vars body env)
  (proc-val (Procedure vars body env))
)

(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env environment?))
)
(define (init-env) (empty-env))

(define (extend-env* vars vals env)
  (foldl
    (λ (binding acc-env) (extend-env (car binding) (cdr binding) acc-env))
    env (zip vars vals))
)

(define (apply-env env qvar)
  (cases environment env
    (empty-env () (error 'apply-env "binding of ~a not found" qvar))
    (extend-env (var val env2)
      (if (equal? var qvar) val (apply-env env2 qvar))
    )
  )
)
