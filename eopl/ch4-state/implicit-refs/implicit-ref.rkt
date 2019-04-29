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
      ("subroutine" identifier "(" (arbno identifier) ")" Statement)
      Subroutine)

    (Statement ("(" Expression (arbno Expression) ")") SCall)

    ; mutable pair
    (Expression ("pair" "(" Expression "," Expression ")") Pair)
    (Expression ("left" "(" Expression ")") Left)
    (Expression ("right" "(" Expression ")") Right)
    (Expression ("setleft" "(" Expression "," Expression")") SetLeft)
    (Expression ("setright" "(" Expression "," Expression ")") SetRight)
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

    (Call (operator operands) (eval-call operator operands))

    (Letrec (def defs expr) (eval-letrec (cons def defs) expr env))

    ; implicit reference
    (Begin_ (exprs) (last (map eval exprs)))

    ; ex 4.20 letmutable
    (LetMutable (vars vals body)
      (eval-let vars (map (compose newref eval) vals) body env)
    )

    (Var (var) (to-rvalue (apply-env env var)))

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
  ) ; cases
) ; value-of

(define (apply-procedure p args)
  (match p ((Procedure vars body env is-subroutine)
    (if (not (equal? (length args) (length vars)))
      (error 'apply-procedure
        "procedure arity mismatch between ~a (parameters) and ~a (arguments)"
        (length args) (length vars))
      (let ((proc-env (extend-env* vars (map newref args) env)))
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

(define (eval-call operator operands env)
  (let ((proc (expval->proc (value-of operator env)))
        (args (map (λ (a) (value-of a env)) operands)))
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
      (printf "~a\n" (expval->val (eval expr)))
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

    (SCall (op args) (eval-call op args env))
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


((sllgen:make-rep-loop "sllgen> " run-program
   (sllgen:make-stream-parser eopl:lex-spec syntax-spec)))
