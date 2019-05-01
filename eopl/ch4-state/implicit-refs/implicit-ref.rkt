#lang racket

(require "legacy-data.rkt")
(require "../../eopl.rkt")
(require (submod "../store.rkt" global-mutable))

(provide (all-defined-out))

(sllgen:define syntax-spec '(
    (Program (Statement) a-program)

    ; basic expressions
    (Expression (number) Num)
    (Expression (identifier) Var)
    (Expression ("-" "(" Expression "," Expression ")") Diff)
    (Expression ("zero?" "(" Expression ")") Zero?)
    (Expression ("if" Expression "then" Expression "else" Expression) If)

    ; ex 4.17. multi argument let & proc
    (Expression
      ("let" (arbno identifier "=" Expression) "in" Expression)
      Let)
    (Expression ("(" Expression (arbno Expression) ")") Call)

    (Expression
      ("proc" "(" (separated-list identifier ",") ")" Expression)
      Proc)

    ; ex 4.18. mutual recursion support
    (Expression ("letrec" ProcDef (arbno ProcDef) "in" Expression) Letrec)
    (ProcDef
      (identifier "(" (separated-list identifier ",") ")"
        "=" Expression )
      MkProcDef)

    ; implicit references
    (Expression ("begin" (separated-list Expression ";") "end") Begin_)

    (Expression ("set" identifier "=" Expression) Set)
    
    ; ex 4.20. letmutable
    (Expression
      ("letmutable" (arbno identifier "=" Expression) "in" Expression)
      LetMutable)

    ; ex 4.21. setdynamic
    (Expression
      ("setdynamic" identifier "=" Expression "during" Expression)
      SetDynamic)

    ; ex 4.22. statements
    (Statement (identifier "=" Expression) Assign)
    (Statement ("print" Expression) Print)
    (Statement ("{" (separated-list Statement ";") "}") Block)
    (Statement ("if" Expression Statement Statement) SIf)
    (Statement ("while" Expression Statement) While)

    ; ex 4.23. read
    (Statement ("read" identifier) Read)
    
    ; ex 4.24. do-while
    (Statement ("do" Statement "while" Expression) DoWhile)

    ; ex 4.25. initialization when declaring variable
    (Statement
      ("var" (separated-list identifier "=" Expression ",") ";"
       Statement)
      VarDecl)

    ; ex 4.26. "procedure 'declared' in a single block" ???

    ; ex 4.27. subroutine
    (Statement
      ("subroutine" identifier "(" (separated-list identifier ",") ")" Statement)
      Subroutine)

    (Statement ("(" Expression (arbno Expression) ")") SCall)

    ; mutable pair
    (Expression ("pair" "(" Expression "," Expression ")") Pair)
    (Expression ("left" "(" Expression ")") Left)
    (Expression ("right" "(" Expression ")") Right)
    (Expression ("setleft" "(" Expression "," Expression")") SetLeft)
    (Expression ("setright" "(" Expression "," Expression ")") SetRight)

    ; ex 4.29. array
    (Expression ("newarray" "(" Expression "," Expression ")") NewArray)
    (Expression ("arrayref" "(" Expression "," Expression ")") ArrayRef)
    (Expression
      ("arrayset" "(" Expression "," Expression "," Expression ")")
      ArraySet)

    ; ex 4.30. arraylength
    (Expression ("arraylength" "(" Expression ")") ArrayLength)

    ; ex 4.33. call by value
    (Expression ("[" Expression (arbno Expression) "]") CallV)
    (Statement ("[" Expression (arbno Expression) "]") SCallV)

    ; ex 4.34. letref
    (Expression
      ("letref" (arbno identifier "=" Expression) "in" Expression)
      Letref)

    ; ex 4.35. ref specifier in pass-by-value framework
    (Expression ("ref" identifier) Ref)

    ; call by name
    (Expression ("<" Expression (arbno Expression) ">") CallN)

    ; ex 4.42 letlazy
    (Expression
      ("letlazy" (arbno identifier "=" Expression) "in" Expression)
      LetLazy)
))

(sllgen:make-define-datatypes eopl:lex-spec syntax-spec)
(define parse (sllgen:make-string-parser eopl:lex-spec syntax-spec))

(define (value-of expr env)
  (define (eval e) (value-of e env))
  (cases Expression expr
    (Num (n) (num-val n))
    (Diff (lhs rhs)
      (num-val (- (expval->num (eval lhs)) (expval->num (eval rhs))))
    )

    (Zero? (expr) (bool-val (zero? (expval->num (eval expr)))))

    (If (test texpr fexpr)
      (if (expval->bool (eval test)) (eval texpr) (eval fexpr))
    )

    (Let (vars vals body)
      (eval-let vars (map eval vals) body env)
    )

    (Proc (params body) (make-procedure-val params body env))

    (Call (operator operands) (eval-call operator operands env 'by-reference))

    (Letrec (def defs expr) (eval-letrec (cons def defs) expr env))

    ; implicit reference
    (Begin_ (exprs) (last (map eval exprs)))

    ; ex 4.20 letmutable
    (LetMutable (vars vals body)
      (eval-let vars (map (compose try-pass-reference eval) vals) body env)
    )

    (Var (var) (eval-var var env))

    (Set (ident expr)
      (define ref (get-ref ident env))
      (setref! ref (eval expr))
      (void-val)
    )

    ; ex 4.21
    (SetDynamic (ident expr body)
      (let* ((ref (get-ref ident env))
             (oldval (deref ref)))
        (setref! ref (eval expr))
        (define result (eval body))
        (setref! ref oldval)
        result
      )
    )

    ; mutable pair
    (Pair (lhs rhs) (pair-val (make-pair (eval lhs) (eval rhs))))
    (Left (expr) (left (expval->pair (eval expr))))
    (Right (expr) (right (expval->pair (eval expr))))
    (SetLeft (pexpr vexpr)
      (set-left (expval->pair (eval pexpr)) (eval vexpr))
    )
    (SetRight (pexpr vexpr)
      (set-right (expval->pair (eval pexpr)) (eval vexpr))
    )

    ; ex 4.29.
    (NewArray (lexpr vexpr)
      (let ((len (expval->num (eval lexpr))))
        (array-val (new-array len (repeat len (eval vexpr))))
      )
    )
    (ArrayRef (arr idx)
      (array-ref (expval->array (eval arr)) (expval->num (eval idx)))
    )
    (ArraySet (arr idx val)
      (array-set
        (expval->array (eval arr)) (expval->num (eval idx)) (eval val))
      (void-val)
    )

    ; ex 4.30.
    (ArrayLength (arr) (array-length (expval->array (eval arr))))

    ; ex 4.33.
    (CallV (operator operands) (eval-call operator operands env 'by-value))

    ; ex 4.34.
    (Letref (vars vals body)
      (eval-let vars (map (eval-as-ref env) vals) body env)
    )

    ; ex 4.35.
    (Ref (ident) (eval-ref ident env))

    ; call by name
    (CallN (operator operands) (eval-call operator operands env 'by-name))

    ; ex 4.42 lazy let
    (LetLazy (vars vals body)
      (eval-let vars (map (eval-as-thunk env) vals) body env)
    )
  ) ; cases
) ; value-of

(define (apply-procedure p args)
  (match p ((Procedure vars body env is-subroutine)
    (if (not (equal? (length args) (length vars)))
      (error 'apply-procedure
        "procedure arity mismatch between ~a (parameters) and ~a (arguments)"
        (length args) (length vars))
      (let ((proc-env (extend-env* vars args env)))
        ((if is-subroutine run-statement-void value-of) body proc-env)
      )
    )
  ))
)

(define (eval-let vars vals body env)
  (let ((new-env (extend-env* vars vals env)))
    (value-of body new-env)
  )
)

(define (eval-call operator operands env eval-strategy)
  ; ex 4.33. support call by value as well
  (define (eval-by-value expr) (try-pass-reference (value-of expr env)))
  (define (select-strategy es)
    (case es
      ((by-value) eval-by-value)
      ((by-reference) (eval-as-ref env))
      ((by-name) (eval-as-thunk env))
    )
  )

  (let ((proc (expval->proc (value-of operator env)))
        (args (map (select-strategy eval-strategy) operands)))
    (apply-procedure proc args)
  )
)

(define (eval-letrec recdefs expr env)
  (define (ProcDef->ProcInfo recdef)
    (cases ProcDef recdef
      (MkProcDef (var params body) (ProcInfo var params body))
    )
  )
  (define (make-rec-env recdefs env)
    (extend-env*-rec (map ProcDef->ProcInfo recdefs) env)
  )
  (let ((rec-env (make-rec-env recdefs env)))
    (value-of expr rec-env)
  )
)

; ex 4.20.
(define (to-rvalue val)
  (cond
    ((reference? val) (deref val))
    ((expval? val) val)
    (else (error 'to-rvalue "invalid expressed value ~a" val))
  )
)

(define (get-ref ident env)
  (define ref (apply-env env ident))
  (unless (reference? ref)
    (error 'get-ref "attempting to set a non-reference value ~a" ref)
  )
  ref
)

(define (eval-var ident env)
  (define ref (apply-env env ident))
  (cond
    ((reference? ref)
      (define tk (deref ref))
      (if (Thunk? tk) (eval-thunk tk) tk)
    )
    ((expval? ref) ref)
    (else 'Var "invalid denoted value ~a" ref)
  )
)

; ex 4.22.
(define (run-program pgm)
  (cases Program pgm
    (a-program (stmt)
      (initialize-store!)
      (run-statement-void stmt (init-env))
    )
  )
)

(define (run-statement stmt env)
  (define (eval e) (value-of e env))
  (define (run stmt) (run-statement stmt env))
  (define (run-block . stmts) (run (Block stmts)))
  (cases Statement stmt
    (Assign (ident expr)
      (let ((ref (get-ref ident env))) (setref! ref (eval expr)))
      env
    )
    (Print (expr)
      (printf "~a\n" (expval->lisp (eval expr)))
      env
    )
    (Block (stmts)
      (foldl
        (λ (cur-stmt cur-env) (run-statement cur-stmt cur-env))
        env stmts)
      env
    )
    (SIf (test tstmt fstmt)
      (if (expval->bool (eval test)) (run tstmt) (run fstmt))
    )
    (While (test stmt)
      (when (expval->bool (eval test)) (run-block stmt (While test stmt)))
      env
    )

    ; ex 4.23.
    (Read (ident)
      (let ((ref (get-ref ident env))) (setref! ref (num-val (read))))
      env
    )

    ; ex 4.24.
    (DoWhile (stmt test) (run-block stmt (While test stmt)))

    ; ex 4.25.
    (VarDecl (idents exprs stmt)
      (run-statement stmt (var-extend-env idents exprs env))
    )

    ; ex 4.27.
    (Subroutine (ident params body)
      (extend-env ident (make-subroutine-val params body env) env)
    )

    (SCall (op args) (eval-call op args env 'by-reference) env)

    ; ex 4.33.
    (SCallV (op args) (eval-call op args env 'by-value) env)
  )
)

(define (run-statement-void stmt env)
  (run-statement stmt env)
  (void)
)

; ex 4.25.
(define (var-extend-env idents exprs env)
  (foldl
    (λ (idexpr acc)
      (extend-env (car idexpr) (newref (value-of (cdr idexpr) acc)) acc)
    )
    env (zip idents exprs))
)

(define (to-lvalue val)
  (if (reference? val) val (newref val))
)

; ex 4.32. call by reference for multiple parameter procedure
(define ((eval-as-ref env) expr)
  (cases Expression expr
    (Var (ident) (to-lvalue (apply-env env ident))) 
    ; ex 4.36. arrayref call by reference
    (ArrayRef (arr idx)
      (array-get-ref
        (expval->array (value-of arr env))
        (expval->num (value-of idx env)))
    )
    (Ref (ident) (to-lvalue (apply-env env ident)))
    (else (newref (value-of expr env)))
  )
)

; ex 4.35.
(define (eval-ref ident env)
  (define ref (apply-env env ident))
  (if (reference? ref) (ref-val ref)
    (error 'Ref "taking reference to a constant")
  )
)

(define (try-pass-reference val)
  (cases expval val
    (ref-val (ref) ref)
    (else (newref val))
  )
)

; call by name
(struct Thunk (body env) #:transparent)

(define (eval-thunk thunk)
  (match thunk ((Thunk body env)
    (value-of body env)
  ))
)

(define ((eval-as-thunk env) expr)
  (cases Expression expr
    (Var (ident) (to-lvalue (apply-env env ident)))
    (Ref (ident) (to-lvalue (apply-env env ident)))

    ; ex 4.41 avoid making thunk when encountering constants
    (Num (n) (newref (num-val n)))
    (Proc (params body) (newref (value-of env expr)))

    (else (newref (Thunk expr env)))
  )
)

((sllgen:make-rep-loop "sllgen> " run-program
   (sllgen:make-stream-parser eopl:lex-spec syntax-spec)))
