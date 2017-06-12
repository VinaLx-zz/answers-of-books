#lang racket

; sicp implementation of the Query language

(provide (all-defined-out))
(require (only-in "eval.rkt" tagged-list?))

(define (query-driver-loop)
  (display "query> ")
  (let ([q (query-syntax-process (read))])
    (cond [(assertion-to-be-added? q)
            (add-rule-or-assertion! (add-assertion-body q))
            (display "Assertion added\n")
            (query-driver-loop)]
          [else
            (display-stream
              (stream-map
                (λ (frame)
                  (instantiate-frame q frame
                    (λ (v f) (contract-question-mark v))))
                (qeval q (singleton-stream empty))))
            (query-driver-loop)])))

(define (instantiate-frame expr frame unbound-var-handler)
  (define (copy expr)
    (cond [(var? expr)
            (let ([binding (binding-in-frame expr frame)])
              (if binding (copy (binding-value binding))
                (unbound-var-handler expr frame)))]
          [(pair? expr)
            (cons (copy (car expr) (copy (cdr expr))))]
          [else expr]))
  (copy expr))

(define (qeval query frame-stream)
  (let ([qproc (get (type query) 'qeval)])
    (if qproc
      (qproc (contents query) frame-stream)
      (simple-query query frame-stream))))

(define (stream-flatmap f s)
  (if (stream-empty? s) empty-stream
    (stream-append (f (stream-first s)) (stream-flatmap f s))))

(define (interleave-delayed s1 delayed-s2)
  (if (stream-empty? s1) (force s2)
    (stream-cons (stream-first s1)
                 (interleave-delayed (force delayed-s2)
                                     (delay (stream-rest s1))))))

(define (singleton-stream e) (stream e))

(define (simple-query pattern frame-stream)
  (stream-flatmap
    (λ (frame)
      (stream-append
        (find-assertions query-pattern frame)
        (apply-rules query-pattern frame)))
    frame-stream))

(define (conjoin conjuncts frame-stream)
  (if (empty-conjunction? conjuncts) frame-stream
    (conjoin (rest-conjuncts conjuncts)
      (qeval (first-conjunct conjuncts) frame-stream))))

(define (disjoin disjuncts frame-stream)
  (if (empty-disjuntion? disjuncts) empty-stream
    (interleave-delayed
      (qeval (first-disjunct disjuncts) frame-stream)
      (delay (disjoin (rest-disjuncts disjuncts) frame-stream)))))


(define (negate operands frame-stream)
  (stream-flatmap
    (λ (frame)
      (if (stream-empty?
            (qeval (negated-query operands) (singleton-stream frame)))
        (singleton-stream frame)
        empty-stream))))

(define (lisp-value call frame-stream)
  (stream-flatmap
    (λ (frame)
      (if (execute (instantiate-frame call frame
                     (λ (v f) (error 'lisp-value "unknown pattern var: ~a" v))))
        (singleton-stream frame)
        empty-stream))
    frame-stream))

(define (execute expr) (apply (eval (predicate expr)) (args expr)))

(define (always-true ignore frame-stream) frame-stream)

; what on earth is put and get???
(put 'and 'qeval conjoin)
(put 'or 'qeval disjoin)
(put 'not 'qeval negate)
(put 'lisp-value 'qeval lisp-value)
(put 'always-true 'qeval always-true)

(define (find-assertions pattern frame)
  (stream-flatmap
    (λ (datum) (check-an-assertion datum pattern frame))
    (fetch-assertions pattern frame)))

(define (check-an-assertion assertion pattern frame)
  (let ([match-result (pattern-match pattern assertion frame)])
    (if match-result (singleton-stream match-result) empty-stream)))

(define (pattern-match pattern datum frame)
  (cond [(equal? frame false) false]
        [(equal? pattern datum) frame]
        [(var? pattern) (extend-if-consistent pattern datum frame)]
        [(and (pair? pattern) (pair datum))
          (pattern-match (cdr pattern) (cdr datum)
            (pattern-match (car pattern) (car datum) frame))]
        [else false]))

(define (extend-if-consistent var datum frame)
  (let ([binding (binding-in-frame var frame)])
    (if binding
      (pattern-match (binding-value binding) datum frame)
      (extend var datum frame))))

(define (apply-rules pattern frame)
  (stream-flatmap
    (λ (rule) (apply-a-rule rule pattern frame))
    (fetch-rules pattern frame)))

(define (apply-a-rule rule pattern frame)
  (let* ([clean-rule (rename-variables-in rule)]
         [unify-result (unify-match pattern (conclusion clean-rule) frame)])
    (if unify-result
      (qeval (rule-body clean-rule) (singleton-stream unify-result))
      empty-stream)))

(define (rename-variables-in rule)
  (let ([rule-application-id (new-rule-application-id)])
    (define (tree-walk expr)
      (cond [(var? expr) (make-new-variable expr new-rule-application-id)]
            [(pair? expr) (cons (tree-walk (car expr)) (tree-walk (cdr expr)))]
            [else expr]))
    (tree-walk rule)))

(define (unify-match p1 p2 frame)
  (cond [(equal? frame false) false]
        [(equal? p1 p2) frame]
        [(var? p1) (extend-if-possible p1 p2 frame)]
        [(var? p2) (extend-if-possible p2 p1 frame)]
        [(and (pair? p1) (pair? p2))
          (unify-match (cdr p1) (cdr p2)
            (unify-match (car p1) (car p2) frame))]
        [else false]))

(define (extend-if-possible var val frame)
  (let ([binding (binding-in-frame var frame)])
    (cond [binding (unify-match (binding-value binding) val frame)]
          [(var? val)
            (let ([binding (binding-in-frame val frame)])
              (if binding (unify-match var (binding-value binding) frame)
                (extend var val frame)))]
          [(depends-on? val var frame) false]
          [else (extend var val frame)])))

(define (depends-on? expr var frame)
  (define (tree-walk e)
    (cond [(var? e)
            (if (equal? var e) true
              (let ([b (binding-in-frame e frame)])
                (if b (tree-walk (binding-value b)) false)))]
          [(pair? e) (or (tree-walk (car e) (cdr e)))]
          [else false]))
  (tree-walk expr))

(define THE-ASSERTIONS empty-stream)
(define THE-RULES empty-stream)

(define (fetch-assertions pattern frame)
  (if (use-index? pattern) (get-indexed-assertions pattern)
    (get-all-assertions)))
(define (get-all-assertions) THE-ASSERTIONS)
(define (get-indexed-assertions pattern)
  (get-stream (index-key-of pattern) 'assertion-stream))
(define (get-stream k1 k2)
  (let ([s (get k1 k2)]) (if s s empty-stream)))

(define (fetch-rules pattern frame)
  (if (use-index? pattern)
    (get-indexed-rules pattern) (get-all-rules)))
(define (get-all-rules) THE-RULES)
(define (get-indexed-rules pattern)
  (stream-append
    (get-stream (index-key-of pattern) 'rule-stream)
    (get-stream '? 'rule-stream)))

(define (add-rule-or-assertion! assertion)
  (if (rule? assertion) (add-rule! assertion) (add-assertion! assertion)))
(define (add-assertion! assertion)
  (let ([old-assertions THE-ASSERTIONS])
    (set! THE-ASSERTIONS (stream-cons assertion old-assertions)))
  'ok)
(define (add-rule! rule)
  (let ([old-rules THE-RULES])
    (set! THE-RULES (stream-cons rule old-rules)))
  'ok)
(define (store-assertion-in-index assertion)
  (if (indexable? assertion)
    (let* ([key (index-key-of assertion)]
           [current-assertion-stream (get-stream key 'assertion-stream)])
      (put key 'assertion-stream
        (cons-stream assertion current-assertion-stream)))
    (void)))
(define (store-rule-in-index rule)
  (let ([pattern (conclusion rule)])
    (if (indexable? pattern)
      (let* ([key (index-key-of pattern)]
             [current-rule-stream (get-stream key 'rule-stream)])
        (put key 'rule-stream
          (cons-stream rule current-rule-stream)))
      (void))))

(define (indexable? pattern)
  (or (constant-symbol? (car pattern)) (var? (car pattern))))
(define (index-key-of pattern)
  (let ([key (car pattern)])
    (if (var? key) '? key)))
(define (use-index? pattern) (constant-symbol? (car pattern)))

(define (type expr)
  (if (pair? expr) (car expr)
    (error 'type "unknown expression type: ~a" expr)))

(define (contents expr)
  (if (pair? expr) (cdr expr)
    (error 'contents "unknown expression contents: ~a" expr)))

(define (assertion-to-be-added? expr) (eq? (type expr) 'assert!))
(define (add-assertion-body expr) (car (contents expr)))

(define empty-conjunction? empty?)
(define empty-disjuntion? empty?)
(define rest-conjuncts cdr)
(define first-conjunct car)
(define rest-disjuncts cdr)
(define first-disjunct car)
(define negated-query car)
(define predicate car)
(define args cdr)

(define rule? (tagged-list? 'rule))
(define conclusion cadr)
(define (rule-body rule)
  (if (null? (cddr rule)) '(always-true) (caddr rule)))

(define (query-syntax-process expr)
  (map-over-symbols expand-question-mark expr))
(define (map-over-symbols proc expr)
  (cond [(pair? expr)
          (cons (map-over-symbols proc (car expr)))]
        [(symbol? expr) (proc expr)]
        [else expr]))
(define (expand-question-mark symbol)
  (let ([chars (symbol->string symbol)])
    (if (string=? (substring chars 0 1) "?")
      (list '? (string->symbol (substring chars 1 (string-length chars))))
      symbol)))

(define var? (tagged-list? '?))
(define constant-symbol? symbol?)

(define rule-counter 0)
(define (new-rule-application-id)
  (begin0 rule-counter (set! rule-counter (add1 rule-counter))))
(define (make-new-variable var rule-application-id)
  (cons '? (cons rule-application-id (cdr var))))
(define (contract-question-mark variable)
  (string->symbol
    (string-append "?"
      (if (number? (cadr variable))
        (string-append (symbol->string (caddr variable))
          "-" (number->string (cadr variable)))
        (symbol->string (cadr variable))))))

(define make-binding cons)
(define binding-value cdr)
(define binding-variable car)
(define binding-in-frame assoc)
(define (extend variable value frame)
  (cons (make-binding variable value) frame))
