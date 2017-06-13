#lang racket

(provide (all-defined-out))

(define (make-machine registers ops controller)
  (let ([machine (make-new-machine)])
    (for-each (λ (register) ((machine 'allocate-register) register))
      registers)
    ((machine 'install-operations) ops)
    ((machine 'install-instruction-sequence)
      (assemble controller machine))
    machine))

(define (make-register name)
  (let ([data '*undefined])
    (define (dispatch msg)
      (case msg
        [(get) data]
        [(set) (λ (value) (set! data value))]
        [else (error 'register "unknown request: ~a" msg)]))
    dispatch))

(define (get-contents reg) (reg 'get))
(define (set-contents reg value) ((reg 'set) value))

(define (make-stack)
  (let ([stack empty])
    (define (push x) (set! stack (cons x stack)))
    (define (pop)
      (if (empty? stack) (error 'pop "empty stack")
        (set! stack (cdr stack))))
    (define (initialize) (set! stack empty))
    (define (dispatch msg)
      (case msg
        [(push) push]
        [(pop) (pop)]
        [(initialize) (initialize)]
        [else (error 'stack "unknown request")]))
    dispatch))

(define (pop stack) (stack 'pop))
(define (push stack value) ((stack 'push) value))

(define (make-new-machine)
  (let* ([pc (make-register 'pc)]
         [flag (make-register 'flag)]
         [stack (make-stack)]
         [instruction-seq empty]
         [ops (hash 'initialize-stack (λ () (stack 'initialize)))]
         [register-table (hash 'pc pc 'flag flag)])
    (define (allocate-register name)
      (if (hash-ref register-table name false)
        (error 'allocate-register "multiply defined register: ~a" name)
        (hash-set! register-table name (make-register name))))
    (define (lookup-register name)
      (let ([register (hash-ref register-table name false)])
        (if register register
          (error 'lookup-register "unknown register: ~a" name))))
    (define (install-operations new-ops)
      (for-each (λ (op) (hash-set! ops (car op) (cadr op))) new-ops))
    (define (execute)
      (let ([insts (get-contents pc)])
        (if (empty? insts) 'done
          (begin ((instruction-execution-proc (car insts)))
                 (execute)))))
    (define (dispatch msg)
      (case msg
        [(start) (set-contents pc instruction-seq)
                 (execute)]
        [(install-instruction-sequence)
         (λ (seq) (set! instruction-seq seq))]
        [(allocate-register) allocate-register]
        [(get-register) lookup-register]
        [(install-operations) install-operations]
        [(stack) stack]
        [(operations) ops]
        [else (error 'machine "unknown request: ~a" msg)]))
    dispatch))

(define (start machine) (machine 'start))
(define (get-register-contents machine name)
  (get-contents (get-register machine name)))
(define (set-register-contents! machine name value)
  (set-contents (get-register machine name) value))
(define (get-register machine name)
  ((machine 'get-register) name))

(define (assemble controller machine)
  (extract-labels controller
    (λ (insts labels)
      (update-insts! insts labels machine)
      insts)))

(define (extract-labels text receive)
  (if (empty? text) (receive empty empty)
    (extract-labels (cdr text)
      (λ (insts labels)
        (let ([next-inst (car text)])
          (if (symbol? next-inst)
            (receive insts (cons (make-label-entry next-inst insts) labels))
            (receive (cons (make-instruction next-inst) insts) labels)))))))

(define (update-insts! insts labels machine)
  (let ([pc (get-register machine 'pc)]
        [flag (get-register machine 'flag)]
        [stack (machine 'stack)]
        [ops (machine 'operations)])
    (for-each
      (λ (inst)
        (set-instruction-execution-proc! inst
          (make-execution-procedure (instruction-text inst)
            labels machine pc flag stack ops)))
      insts)))

(define (make-instruction text) (mcons text empty))
(define (instruction-text inst) (mcar inst))
(define (instruction-execution-proc inst) (mcdr inst))
(define (set-instruction-execution-proc! inst proc)
  (set-mcdr! inst proc))

(define make-label-entry cons)
(define (lookup-label labels name)
  (let ([val (assoc name labels)])
    (if val (cdr val) (error 'lookup-label "undefined label: ~a" name))))

(define (make-execution-procedure
          inst labels machine pc flag stack ops)
  (case (car inst)
    [('assign) (make-assign inst machine labels ops pc)]
    [('test) (make-test inst machine labels ops flag pc)]
    [('branch) (make-branch inst machine labels ops flag pc)]
    [('goto) (make-goto inst machine labels pc)]
    [('save) (make-save inst machine stack pc)]
    [('restore) (make-restore inst machine stack pc)]
    [('perform) (make-perform inst machine labels ops pc)]
    [else (error 'make-execution-procedure "unknown instruction type: ~a" (car inst))]))

(define (make-assign inst machine labels operations pc)
  (let* ([target (get-register machine (assign-reg-name inst))]
         [value-expr (assign-value-expr inst)]
         [value-proc
            (if (operation-expr? value-expr)
              (make-operation-expr value-expr machine labels operations)
              (make-primitive-expr (car value-expr) machine labels))])
    (λ () (set-contents target (value-proc)) (advance-pc pc))))

(define assign-reg-name cadr)
(define assign-value-expr cddr)
(define (advance-pc pc) (set-contents pc (cdr (get-contents pc))))

(define (make-test
          inst machine labels operations flag pc)
  (let ([condition (test-condition inst)])
    (if (not (operation-expr? condition))
      (error 'make-test "bad test instruction: ~a" inst)
      (let ([condition-proc
             (make-operation-expr condition machine labels operations)])
        (λ () (set-contents flag (condition-proc))
              (advance-pc pc))))))
(define test-condition cdr)

(define (make-branch
          inst machine labels flag pc)
  (let ([dest (branch-dest inst)])
    (if (not (label-expr? dest))
      (error 'make-branch "bad branch instruction: ~a" inst)
      (let ([insts (lookup-label labels (label-expr-label))])
        (λ ()
          (if (get-contents flag)
            (set-contents pc insts)
            (advance-pc pc)))))))
(define branch-dest cadr)

(define (make-goto inst machine labels pc)
  (let ([dest (goto-dest inst)])
    (cond [(label-expr? dest)
             (let ([insts (lookup-label labels (label-expr-label dest))])
               (λ () (set-contents pc insts)))]
          [(register-expr? dest)
             (let ([reg (get-register machine (register-expr-reg dest))])
               (λ () (set-contents pc (get-contents reg))))]
          [else (error 'make-goto "bad goto instruction: ~a" inst)])))
(define goto-dest cadr)

(define (make-save inst machine stack pc)
  (let ([reg (get-register machine (stack-inst-reg-name) inst)])
    (λ () (push stack (get-contents reg)) (advance-pc pc))))

(define (make-restore inst machine stack pc)
  (let ([reg (get-register machine (stack-inst-reg-name inst))])
   (λ () (set-contents reg (pop stack)) (advance-pc pc))))
(define stack-inst-reg-name cadr)

(define (make-perform inst machine labels operations pc)
  (let ([action (perform-action inst)])
    (if (not (operation-expr? action))
      (error 'make-perform "bad perform instruction: ~a" inst)
      (let ([action-proc
             (make-operation-expr action machine labels operations)])
        (λ () (action-proc) (advance-pc))))))
(define perform-action cdr)

(define (make-primitive-expr expr machine labels)
  (cond [(constant-expr? expr)
           (let ([c (constant-expr-value expr)])
             (λ () c))]
        [(label-expr? expr)
           (let ([insts (lookup-label labels (label-expr-label expr))])
             (λ () insts))]
        [(register-expr? expr)
           (let ([r (get-register machine (register-expr-reg expr))])
             (λ () (get-contents r)))]
        (else (error 'make-primitive-expr "unknown exprssion type ~a" expr))))

(define ((tagged-list? name) l) (eq? (car l) name))

(define register-expr? (tagged-list? 'reg))
(define register-expr-reg cadr)
(define constant-expr? (tagged-list? 'const))
(define constant-expr-value cadr)
(define label-expr? (tagged-list? 'label))
(define label-expr-label cadr)

(define (make-operation-expr expr machine labels operations)
  (let ([op (lookup-prim (operation-expr-op expr) operations)]
        [aprocs (map
                  (λ (e) (make-primitive-expr e machine labels))
                  (operation-expr-operands expr))])
    (λ () (apply op (map (λ (p) (p)) aprocs)))))

(define (operation-expr? expr)
  (and (pair? expr) ((tagged-list? 'op) (car expr))))
(define (operation-expr-op expr)
  (cadr (car expr)))
(define operation-expr-operands cdr)
(define (lookup-prim symbol operations)
  (let ([val (hash-ref operations symbol false)])
    (if val val
      (error "unknown operation: ~a" symbol))))
