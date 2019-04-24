#lang racket

(require "../eopl.rkt")
(provide (all-defined-out))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))

  ; ex 3.9.
  (list-val (l list?))

  ;; proc
  (proc-val (proc Procedure?))
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

; ex 3.9.
(define (expval->list val)
  (cases expval val
    (list-val (l) l)
    (else (report-expval-extractor-error 'list val))
  )
)

(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (list-val (l) l)

    ;; proc
    (proc-val (p) p)
  )
)

;; proc
(define (expval->proc val)
  (cases expval val
    (proc-val (p) p)
    (else (report-expval-extractor-error 'proc val))
  )
)


;; proc
(struct Procedure (vars body env) #:transparent)

(struct ProcInfo (name params body) #:transparent)

; ex 3.26. shrink the environment in procedure
;   Ideally we traverse the body with formal parameters, identifying all free
;   variables, and apply the environment by those variables and construct a new
;   environment of only those free variables.
;   But traversing the procedure body is too laborious and subjects to change
;   with latter exercises. So I omit the implementation
(define (make-procedure-val vars body env)
  (proc-val (Procedure vars body env))
)

(module* procedural #f
  (define (empty-env)
    (λ (var) (error 'env "binding of ~a not found" var))
  )
  (define environment? procedure?)

  (define (extend-env var val env)
    (λ (qvar) (if (equal? qvar var) val (env qvar)))
  )
  (define (apply-env env var) (env var))

  (define (extend-env* vars vals env)
    (foldl
      (λ (binding acc-env) (extend-env (car binding) (cdr binding) acc-env))
      env (zip vars vals))
  )

  ; ex 3.32. 3.33
  (define (extend-env*-rec proc-infos env)
    (λ (qvar)
      (let* ((predicate (λ (info) (equal? qvar (ProcInfo-name info))))
             (proc-info (findf predicate proc-infos)))
        (if proc-info
          (match proc-info ((ProcInfo _ params body)
            (make-procedure-val params body (extend-env*-rec proc-infos env))
          ))
          (env qvar)
        )
      )
    ) ; env
  )
  ; ex 3.34
  (define (extend-env-rec var params body env)
    (extend-env*-rec (list (ProcInfo var params body)) env)
  )
)

; ex 3.35. data representation of recursive environment
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

; ex 3.36. support mutual recursion
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
            (make-procedure-val params body env)
          ))
          (apply-env env qvar)
        )
      )
    )
  )
)
