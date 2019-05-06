#lang racket

(require "../eopl.rkt")
(require (submod "../ch4-state/store.rkt" global-mutable))
(provide (all-defined-out))
(require "cont.rkt")
(require "thread/thread.rkt")
(require "thread/mutex.rkt")
(require "thread/condition-variable.rkt")

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc Procedure?))
  (list-val (xs (list-of expval?)))
  (void-val)

  ; ex 5.40
  (cont-val (cont cont?))

  ; mutex
  (mutex-val (mtx mutex?))

  ; ex 5.51. ex 5.57.
  (condvar-val (cond-var condition-variable?))

  ; ex 5.53. thread id
  (tid-val (id thread-id?))
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
(define (expval->list val)
  (cases expval val
    (list-val (l) l)
    (else (report-expval-extractor-error 'list val))
  )
)
(define (expval->cont val)
  (cases expval val
    (cont-val (cont) cont)
    (else (report-expval-extractor-error 'cont val))
  )
)
(define (expval->mutex val)
  (cases expval val
    (mutex-val (mtx) mtx)
    (else (report-expval-extractor-error 'mutex val))
  )
)
(define (expval->condvar val)
  (cases expval val
    (condvar-val (cv) cv)
    (else (report-expval-extractor-error 'cond-var val))
  )
)
(define (expval->tid val)
  (cases expval val
    (tid-val (tid) tid)
    (else (report-expval-extractor-error 'thread-id val))
  )
)
(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (list-val (l) (map expval->val l))
    (void-val () (void))
    (cont-val (c) c)
    (mutex-val (m) m)
    (condvar-val (cv) cv)
    (tid-val (t) t)
  )
)
(struct Procedure (vars body env) #:transparent)
(struct ProcInfo (name params body) #:transparent)

(define (make-procedure-val vars body env)
  (proc-val (Procedure vars body env))
)
(define-datatype environment environment?
  (empty-env)
  (extend-env (var symbol?) (val reference?) (env environment?))
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
            (newref (make-procedure-val params body env))
          ))
          (apply-env env2 qvar)
        )
      )
    )
  )
)
