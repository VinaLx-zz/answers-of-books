#lang racket

(provide (all-defined-out))

; ex 2.5. a-list representation of env
(module a-list racket
  (provide (all-defined-out))
  (define (empty-env) null)

  (define (extend-env-with-binding binding env) (cons binding env))
  (define (extend-env var val env)
    (extend-env-with-binding (cons var val) env)
  )

  (define (apply-env env var)
    ; ex 2.7. more informative error message
    (define (report-no-binding-found)
      (error 'apply-env "No binding for ~a in ~a\n" var env))
    (define (apply-env-impl env)
      (if (empty-env? env) (report-no-binding-found)
        (let ((env-var (car (car env)))
              (env-val (cdr (car env))))
          (if (equal? env-var var) env-val
            (apply-env-impl (cdr env))
          )
        ) ; non-empty-env
      ) ; if empty-env?
    )
    (apply-env-impl env)
  ) 

  ; ex 2.8. empty-env?
  (define empty-env? null?)
  
  ; ex 2.9. has-binding?
  (define (has-binding? env var)
    (ormap (λ (binding) (equal? (car binding) var)) env)
  )
  
  ; ex 2.10. extend-env*
  (define (extend-env* vars vals env)
    (define (zip l1 l2)
      (if (or (null? l1) (null? l2)) null
        (cons (cons (car l1) (car l2)) (zip (cdr l1) (cdr l2)))
      )
    )
    (foldr
      (λ (new-binding new-env)
        (extend-env-with-binding new-binding new-env)
      ) env (zip vars vals))
  )
)

(require 'a-list)
(provide (all-from-out 'a-list))

; ex 2.11. ribcage
(module ribcage racket
  (provide (all-defined-out))

  (define (empty-env) null)
  (define empty-env? null?)

  (define (extend-new-rib vars vals env) (cons (cons vars vals) env))
  (define (extend-rib var val rib)
    (cons
      (cons var (car rib))
      (cons val (cdr rib)))
  )
  (define (extend-env var val env)
    (if (empty-env? env)
      (extend-new-rib (list var) (list val) env)
      (cons (extend-rib var val (car env)) (cdr env))
    )
  )
  (define (apply-env env var)
    (define (report-no-binding-found)
      (error 'apply-env "No binding for ~a in ~a\n" var env))
    (define (apply-rib rib var)
      (define (apply-rib-impl vars vals var)
        ; implies (null? vals)
        (cond
          ((null? vars) 'rib-not-found)
          ((equal? (car vars) var) (car vals))
          (else (apply-rib-impl (cdr vars) (cdr vals) var))
        )
      )
      (apply-rib-impl (car rib) (cdr rib) var)
    ) ; apply-rib
    (define (apply-env-impl env)
      (if (empty-env? env) (report-no-binding-found)
        (let ((this-rib-result (apply-rib (car env) var)))
          (if (equal? this-rib-result 'rib-not-found)
            (apply-env-impl (cdr env))
            this-rib-result
          )
        )
      )
    ) ; apply-env-impl
    (apply-env-impl env)
  )
  (define extend-env* extend-new-rib)
)

(require (prefix-in rib: 'ribcage))
(provide (all-from-out 'ribcage))

(module procedural racket
  (provide (all-defined-out))

  ; ex 2.12. procedural stack representation
  (define (empty-stack)
    (λ () (error 'stack "accessing empty stack"))
  )
  (define (push v stack) (λ () (values v stack)))
  (define (pop stack)
    (let-values (((t stk) (stack))) stk)
  )
  (define (top stack)
    (let-values (((t stk) (stack))) t)
  )
  (define (empty-stack? stack)
    (with-handlers
      ((exn:fail? (λ (e) #t)))
      (stack) #f
    )
  )

  ; ex 2.13. ex 2.14.
  ;   extending procedural environment representation to support
  ;   empty-env? and has-binding?
  (define (empty-env)
    (list
      (λ (var) (error 'env "binding of ~a not found" var))
      (λ () #t)    ; empty-env?
      (λ (var) #f) ; has-binding?
    )
  )
  (define (extend-env var val env)
    (list
      (λ (qvar)
        (if (equal? qvar var) val ((car env) qvar))
      )
      (λ () #f)
      (λ (qvar)
        (or (equal? qvar var) ((caddr env) qvar))
      )
    )
  )
  (define (apply-env env var) ((car env) var))
  (define (empty-env? env) ((cadr env)))
  (define (has-binding? env var) ((caddr env) var))
)

(require (prefix-in proc: 'procedural))
(provide (all-from-out 'procedural))
