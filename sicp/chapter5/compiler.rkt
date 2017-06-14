#lang racket

(require "../chapter4/eval.rkt")

(provide (except-out (all-defined-out) make-label))

(define (my-compile expr target linkage)
  (cond [(self-evaluating? expr) (compile-self-evaluating expr target linkage)]
        [(quoted? expr) (compile-quoted expr target linkage)]
        [(variable? expr) (compile-variable expr target linkage)]
        [(assignment? expr) (compile-assignment expr target linkage)]
        [(definition? expr) (compile-definition expr target linkage)]
        [(if-statement? expr) (compile-if expr target linkage)]
        [(lambda-expr? expr) (compile-lambda expr target linkage)]
        [(begin-statement? expr)
           (compile-sequence (begin-actions expr) target linkage)]
        [(cond-statement? expr) (my-compile (cond->if expr) target linkage)]
        [(application? expr) (compile-application expr target linkage)]
        [else (error 'my-compile "unknown expression type: ~a" expr)]))

(define (make-instruction-sequence need modified code)
  (list need modified code))

(define (empty-instruction-sequence)
  (make-instruction-sequence empty empty empty))

(define (compile-linkage linkage)
  (case linkage
    [(return)
       (make-instruction-sequence
         (list 'continue) empty (list '(goto (reg continue))))]
    [(next) (empty-instruction-sequence)]
    [else (make-instruction-sequence
         empty empty (list `(goto (label ,linkage))))]))

(define (end-with-linkage linkage instruction-sequence)
  (preserving (list 'continue)
    instruction-sequence (compile-linkage linkage)))

(define (compile-self-evaluating expr target linkage)
  (end-with-linkage linkage
    (make-instruction-sequence empty (list target)
      (list `(assign ,target (const ,expr))))))

(define (compile-quoted expr target linkage)
  (end-with-linkage linkage
    (make-instruction-sequence empty (list target)
      (list `(assign ,target (const ,(text-of-quotation expr)))))))

(define (compile-variable expr target linkage)
  (end-with-linkage linkage
    (make-instruction-sequence (list 'env) (list target)
      (list `(assign ,target
               (op lookup-variable-value) (const ,expr) (reg env))))))

(define (compile-assignment expr target linkage)
  (let ([var (assignment-variable expr)]
        [value-code (my-compile (assignment-value expr) 'val 'next)])
    (end-with-linkage linkage
      (preserving (list 'env) value-code
        (make-instruction-sequence (list 'env 'val) (list 'target)
          `((perform (op set-variable-value!)
                     (const ,var) (reg val) (reg env))
            (assign ,target (const ok))
           ))))))

(define (compile-definition expr target linkage)
  (let ([var (definition-variable expr)]
        [value-code (my-compile (definition-value expr) 'val 'next)])
    (end-with-linkage linkage
      (preserving (list 'env) value-code
        (make-instruction-sequence (list 'env 'val) (list target)
          `((perform (op define-variable) (const ,var) (reg val) (reg env))
            (assign ,target (const ok))))))))

(define counter 0)
(define (make-label name)
  (begin0
    (string->symbol
      (string-append (symbol->string name) (number->string counter)))
    (set! counter (add1 counter))))

(define (compile-if expr target linkage)
  (let* ([true-label (make-label 'if-true)]
         [false-label (make-label 'if-false)]
         [end-label (make-label 'end-if)]
         [true-linkage (if (eq? linkage 'next) end-label linkage)]
         [predicate-code (my-compile (if-predicate expr) 'val 'next)]
         [true-code (my-compile (if-consequent expr) target true-linkage)]
         [false-code (my-compile (if-alternative expr) target linkage)])
    (preserving (list 'env 'continue) predicate-code
      (append-instruction-sequences
        (make-instruction-sequence (list 'val) empty
          `((test (op exp-false?) (reg val))
            (branch (label ,false-label))))
        (parallel-instruction-sequences
          (append-instruction-sequences true-label true-code)
          (append-instruction-sequences false-label false-code))
        end-label))))

(define (compile-sequence seq target linkage)
  (if (last-exp? seq)
    (my-compile (first-exp seq) target linkage)
    (preserving (list 'env 'continue)
      (my-compile (first-exp seq) target 'next)
      (compile-sequence (rest-exps seq) target linkage))))

(define (make-compiled-procedure entry env)
  (list 'compiled-procedure entry env))
(define compiled-procedure? (tagged-list? 'compiled-procedure?))
(define compiled-procedure-entry cadr)
(define compiled-procedure-env caddr)

(define (compile-lambda expr target linkage)
  (let* ([proc-entry (make-label 'entry)]
         [after-lambda (make-label 'after-lambda)]
         [lambda-linkdage
           (if (eq? linkage 'next) after-lambda linkage)])
    (append-instruction-sequences
      (tack-on-instruction-sequences
        (end-with-linkage lambda-linkdage
          (make-instruction-sequence (list 'env) (list target)
            (list `(assign ,target
                     (op make-compiled-procedure)
                     (label ,proc-entry) (reg env)))))
        (compile-lambda-body expr proc-entry))
      after-lambda)))

(define (compile-lambda-body expr entry)
  (let ([formals (lambda-parameters expr)])
    (append-instruction-sequences
      (make-instruction-sequence (list 'env 'proc 'argl) (list 'env)
        `(,entry
          (assign env (op compiled-procedure-env) (reg proc))
          (assign env (op extend-environment)
            (const ,formals) (reg argl) (reg env))))
      (compile-sequence (lambda-body expr) 'val 'return))))

(define (compile-application expr target linkage)
  (let ([proc-code (my-compile (operator expr) 'proc 'next)]
        [operand-codes
          (map (λ (operand) (my-compile operand 'val 'next))
            (operands expr))])
    (preserving (list 'env 'continue) proc-code
      (preserving (list 'proc 'continue)
        (construct-arglist operand-codes)
        (compile-procedure-call target linkage)))))

(define (construct-arglist operand-codes)
  (let ([codes (reverse operand-codes)]) ; weird implementation...
    (if (empty? codes)
      (make-instruction-sequence empty (list 'argl)
        (list '(assign argl (const ()))))
      (let ([code-to-get-last-arg
              (append-instruction-sequences (car codes)
                (make-instruction-sequence (list 'val) (list 'argl)
                  (list '(assign argl (op list) (reg val)))))])
        (if (empty? (cdr operand-codes)) code-to-get-last-arg
          (preserving (list 'env)
            code-to-get-last-arg
            (code-to-get-rest-args (cdr codes))))))))

(define (code-to-get-rest-args codes)
  (let ([code-for-next-arg
          (preserving '(argl) (car codes)
            (make-instruction-sequence (list 'val 'argl) (list 'argl)
              (list '(assign argl (op cons) (reg val) (reg argl)))))])
    (if (empty? (cdr codes)) code-for-next-arg
      (preserving (list 'env) code-for-next-arg
        (code-to-get-rest-args (cdr codes))))))

(define (compile-procedure-call target linkage)
  (let* ([primitive-label (make-label 'primitive-label)]
         [compiled-label (make-label 'compiled-label)]
         [after-call (make-label 'after-call)]
         [compiled-linkage (if (eq? linkage 'next) after-call linkage)])
    (append-instruction-sequences
      (make-instruction-sequence (list 'proc) empty
        `((test (op primitive-procedure?) (reg proc))
          (branch (label ,primitive-label))))
      (parallel-instruction-sequences
        (append-instruction-sequences compiled-label
          (compile-proc-appl target compiled-linkage))
        (append-instruction-sequences primitive-label
          (end-with-linkage linkage
            (make-instruction-sequence (list 'proc 'argl) (list target)
              (list `(assign ,target
                       (op apply-primitive-procedure) (reg proc) (reg argl)))))))
      after-call)))

(define all-regs (list 'env 'proc 'val 'argl 'continue))

(define (compile-proc-appl target linkage)
  (cond [(and (eq? target 'val) (not (eq? linkage 'return)))
          (make-instruction-sequence (list 'proc) all-regs
            `((assign continue (label ,linkage))
              (assign val (op compiled-procedure-entry) (reg proc))
              (goto (reg val))))]
        [(and (eq? target 'val) (eq? linkage 'return))
          (make-instruction-sequence (list 'proc 'continue) all-regs
            '((assign val (op compiled-procedure-entry) (reg proc))
              (goto (reg val))))]
        [(and (not (eq? target 'val)) (not (eq? target 'return)))
          (make-instruction-sequence
            (let ([proc-return (make-label 'proc-return)])
              `((assign continue (label ,proc-return))
                (assign val (op compiled-procedure-entry) (reg proc))
                (goto (reg val))
                ,proc-return
                (assign ,target (reg val))
                (goto (label ,linkage)))))]
        [(and (not (eq? target 'val)) (eq? linkage 'return))
          (error 'compile-proc-appl
            "return linkage, target not val: ~a" target)]))

(define (register-needed s) (if (symbol? s) empty (car s)))
(define (register-modified s) (if (symbol? s) empty (cadr s)))
(define (statements s) (if (symbol? s) (list s) (caddr s)))

(define (needs-register? seq reg) (memq reg (register-needed seq)))
(define (modifies-register? seq reg) (memq reg (register-modified seq)))

(define (append-instruction-sequences . seqs)
  (define (append-2-sequences seq1 seq2)
    (make-instruction-sequence
      (list-union
        (register-needed seq1)
        (list-difference
          (register-needed seq2) (register-modified seq1)))
      (list-union (register-modified seq1) (register-modified seq2))
      (append (statements seq1) (statements seq2))))
  (define (append-seq-lists seqs)
    (if (empty? seqs) (empty-instruction-sequence)
      (append-2-sequences (car seqs) (append-seq-lists (cdr seqs)))))
  (append-seq-lists seqs))

(define (preserving regs seq1 seq2)
  (if (empty? regs) (append-instruction-sequences seq1 seq2)
    (let ([first-reg (car regs)])
      (if (and (needs-register? seq2 first-reg)
               (modifies-register? seq1 first-reg))
        (preserving (cdr regs)
          (make-instruction-sequence
            (list-union (list first-reg) (register-needed seq1))
            (list-difference (register-modified seq1) (list first-reg))
            (append `((save ,first-reg))
                    (statements seq1)
                    `((restore ,first-reg))))
          seq2)
        (preserving (cdr regs) seq1 seq2)))))

(define (tack-on-instruction-sequences seq body)
  (make-instruction-sequence (register-needed seq) (register-modified seq)
    (append (statements seq) (statements body))))

(define (parallel-instruction-sequences seq1 seq2)
  (make-instruction-sequence
    (list-union (register-needed seq1) (register-needed seq2))
    (list-union (register-modified seq1) (register-modified seq2))
    (append (statements seq1) (statements seq2))))

(define (list-union s1 s2)
  (set->list (set-union (list->set s1) (list->set s2))))
(define (list-difference s1 s2)
  (set->list (set-subtract (list->set s1) (list->set s2))))

