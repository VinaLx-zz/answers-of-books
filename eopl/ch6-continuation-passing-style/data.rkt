#lang racket

(require "../eopl.rkt")
(provide (all-defined-out))
(require (submod "../ch4-state/store.rkt" global-mutable))


(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc Procedure?))
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

(define (expval->ref val)
  (cases expval val
    (ref-val (ref) ref)
    (else (report-expval-extractor-error 'reference val))
  )
)

(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (ref-val (r) r)
  )
)

(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else (report-expval-extractor-error 'proc val))
  )
)

(struct Procedure (vars body env) #:transparent)

(struct ProcInfo (name params body) #:transparent)

(define (make-procedure-val vars body env)
  (proc-val (Procedure vars body env))
)

(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env environment?))
  (extend-env*-rec (proc-infos (list-of ProcInfo?)) (env environment?))
)

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
            ((compose ref-val newref) (make-procedure-val params body env))
          ))
          (apply-env env2 qvar)
        )
      )
    )
  )
)
