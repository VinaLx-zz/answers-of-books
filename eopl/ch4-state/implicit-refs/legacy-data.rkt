#lang racket

;; mostly copied from "ch3-expression/procedure.rkt"

(require "../../eopl.rkt")
(require (submod "../store.rkt" global-mutable))
(require "mutable-pair.rkt")
(provide (all-defined-out))
(provide (all-from-out "mutable-pair.rkt"))

(struct Procedure (vars body env body-is-stmt) #:transparent)

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc Procedure?))
  (void-val)

  ; mutable pair
  (pair-val (p mutable-pair?))
  (array-val (arr array?))

  ; ex 4.35
  (ref-val (ref reference?))
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
(define (expval->pair val)
  (cases expval val
    (pair-val (p) p)
    (else (report-expval-extractor-error 'pair val))
  )
)
(define (expval->array val)
  (cases expval val
    (array-val (a) a)
    (else (report-expval-extractor-error 'array val))
  )
)

(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (void-val () (void))
    (pair-val (p) p)
    (array-val (a) a)
    (ref-val (r) r)
  )
)
(define (expval->lisp val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (void-val () (void))
    (pair-val (p)
      (cons (expval->lisp (left p)) (expval->lisp (right p))))
    (array-val (a) (map (compose expval->lisp deref) (array-data a)))
    (ref-val (r) (expval->lisp (deref r)))
  )
)

(define (make-procedure-val vars body env)
  (proc-val (Procedure vars body env #f))
)
(define (make-subroutine-val vars body env)
  (proc-val (Procedure vars body env #t))
)

(struct ProcInfo (name params body) #:transparent)

(define (pred-or . preds)
  (lambda (v) (ormap (λ (p) (p v)) preds))
)

(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var symbol?) (val (pred-or reference? expval?)) (env environment?)
  )
  (extend-env*-rec (proc-infos (list-of ProcInfo?)) (env environment?))
)
(define (init-env) (empty-env))

(define (extend-env* vars vals env)
  (foldl
    (λ (binding acc-env) (extend-env (car binding) (cdr binding) acc-env))
    env (zip vars vals))
)

(define (extend-env-rec var params body env)
  (extend-env*-rec (list (ProcInfo var params body)) env)
)
(define (apply-env env qvar)
  (cases environment env
    (empty-env () (error 'apply-env "binding of ~a not found" qvar))
    (extend-env (var val env2)
      (if (equal? var qvar) val (apply-env env2 qvar))
    )
    (extend-env*-rec (proc-infos env2)
      (let* ((predicate (λ (info) (equal? qvar (ProcInfo-name info))))
             (proc-info (findf predicate proc-infos)))
        (if proc-info
          (match proc-info ((ProcInfo _ params body)
            ; implicit reference
            (newref (make-procedure-val params body env))
          ))
          (apply-env env qvar)
        )
      )
    )
  )
)
