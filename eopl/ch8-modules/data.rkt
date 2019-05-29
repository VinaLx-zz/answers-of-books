#lang racket

(require "../eopl.rkt")
(require "language.rkt")
(provide (all-defined-out))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc Procedure?))
  (module-val (mod TypedModule?))
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
(define (expval->module val)
  (cases expval val
    (module-val (m) m)
    (else (report-expval-extractor-error 'module val))
  )
)
(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (module-val (m) m)
  )
)

(struct Procedure (vars body env) #:transparent)

(define (make-procedure-val vars body env)
  (proc-val (Procedure vars body env))
)

(struct ProcInfo (name params body) #:transparent)

(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var (p-or symbol? type-var?))
    (val (p-or expval? Type?))
    (env environment?)
  )
  (extend-env*-rec (proc-infos (list-of ProcInfo?)) (env environment?))
)

(define (extend-env* vars vals env)
  (extend-env*/binding (zip vars vals) env)
)

(define (extend-env/binding b env)
  (extend-env (car b) (cdr b) env)
)

(define (extend-env*/binding bs env)
  (foldl (λ (b acc) (extend-env/binding b acc)) env bs)
)

(define (extend-env-rec var params body env)
  (extend-env*-rec (list (ProcInfo var params body)) env)
)

(define (apply-env env qvar (should-throw #t))
  (cases environment env
    (empty-env ()
      (if should-throw
        (error 'apply-env "binding of ~a not found" qvar)
        false
      )
    )
    (extend-env (var val env2)
      (if (equal? var qvar) val (apply-env env2 qvar should-throw))
    )
    (extend-env*-rec (proc-infos env2)
      (let* ((predicate (λ (info) (equal? qvar (ProcInfo-name info))))
             (proc-info (findf predicate proc-infos)))
        (match proc-info
          ((ProcInfo _ params body) (make-procedure-val params body env))
          (#f (apply-env env2 qvar should-throw))
        )
      )
    )
  )
)

;; simple module

(struct TypedModule (bindings) #:transparent)

(define (look-up-qualified-var mvar var env)
  (match-define (TypedModule bindings) (expval->module (apply-env env mvar)))
  (apply-env bindings var)
)

;; opaque types

(struct type-var (type) #:transparent)
