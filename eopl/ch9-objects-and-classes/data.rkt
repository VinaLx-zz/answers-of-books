#lang racket

(require "../eopl.rkt")
(require "language.rkt")
(require (submod "../ch4-state/store.rkt" global-mutable))
(provide (all-defined-out))

(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc Procedure?))
  (list-val (l (list-of expval?)))
  (object-val (o object?))
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
(define (expval->list val)
  (cases expval val
    (list-val (l) l)
    (else (report-expval-extractor-error 'list val))
  )
)
(define (expval->object val)
  (cases expval val
    (object-val (o) o)
    (else (report-expval-extractor-error 'object val))
  )
)
(define (expval->val val)
  (cases expval val
    (num-val (n) n)
    (bool-val (b) b)
    (proc-val (p) p)
    (list-val (l) (map expval->val l))
    (object-val (o) o)
    (void-val () (void))
  )
)

(struct Procedure (params body env) #:transparent)

(define (make-procedure-val params body env)
  (proc-val (Procedure params body env))
)

(struct ProcInfo (name params body) #:transparent)

(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var symbol?)
    (val (p-or reference? expval? Type? method?))
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
          ((ProcInfo _ params body)
            (newref (make-procedure-val params body env)))
          (#f (apply-env env2 qvar should-throw))
        )
      )
    )
  )
)

;; OOP

(require racket/undefined)

(define class-env undefined)

(define (initialize-class-env!)
  (set! class-env (make-hash))
  (extend-class-env! 'object object-class)
)

(define (extend-class-env! name cls)
  (hash-set! class-env name cls)
)

(define (apply-class-env name)
  (hash-ref class-env name)
)

; ex 9.4. ex 9.5. some changes of representation of data

(struct class_ (name super-class field-names method-env) #:transparent)

(define object-class (class_ 'object false null (empty-env)))

(struct method (visibility host-class-name params body) #:transparent)

(struct object (class_ fields-env super-obj) #:transparent)

(define object-class-name (compose class_-name object-class_))

; object -> symbol -> object
(define (target-super-object obj class-name)
  (define (target-super-object-impl obj)
    (if (equal? (object-class-name obj) class-name) obj
      (target-super-object-impl (object-super-obj obj))
    )
  )
  (define result (target-super-object-impl obj))
  (unless result
    (error 'target-super-object
      "object ~v doesn't have super class ~a" obj class-name))
  result
)

; object -> symbol -> method
(define (get-method obj method-name)
  (let* ((cls (object-class_ obj))
         (mthd-env (class_-method-env cls)))
    (apply-env mthd-env method-name)
  )
)

(define (get-field-ref obj field-name)
  (apply-env (object-fields-env obj) field-name)
)

; ex 9.11. ex. 9.12

(define (v-great v1 v2)
  (cases Visibility v1
    (VPrivate () false)
    (VProtected () (cases Visibility v2
      (VPrivate () true)
      (else false)
    ))
    (VPublic () (cases Visibility v2
      (VPublic () false)
      (else true)
    ))
  )
)
(define (v-ge v1 v2) (or (v-great v1 v2) (equal? v1 v2)))

(define (equal-class? cls1 cls2)
  (equal? (class_-name cls1) (class_-name cls2))
)

(define (subclass? c1 c2)
  (cond
    ((not c1) false)
    ((not c2) true)
    ((equal-class? c1 c2) true)
    (else (subclass? (class_-super-class c1) c2))
  )
)

(define (visible? callee-vis callee-cls caller-cls)
  (cond
    ((not caller-cls) (equal? callee-vis (VPublic)))
    ((equal-class? caller-cls callee-cls) true)
    ((subclass? caller-cls callee-cls)
      (v-ge callee-vis (VProtected))
    )
  )
)

