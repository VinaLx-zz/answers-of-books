#lang racket

(provide (all-defined-out))

(require (only-in eopl define-datatype cases))

(define (any? . rest) #t)

; ex 2.21. define-datatype Env
(define-datatype Env Env?
  (empty-env)
  (extend-env (var symbol?) (val any?) (tail Env?))
)

(define (empty-env? e)
  (cases Env e
    (empty-env () #t)
    (extend-env (var val tail) #f)
  )
)

(define (apply-env e var)
  (cases Env e
    (empty-env ()
      (error 'apply-env "invalid variable ~s" var))
    (extend-env (evar eval tail)
      (if (equal? evar var) eval (apply-env tail var)))
  )
)

(define (has-binding? e var)
  (cases Env e
    (empty-env () #f)
    (extend-env (evar eval tail)
      (or (equal? evar var) (has-binding? tail var)))
  )
)

; ex 2.22. define-datatype Stack
(define-datatype Stack Stack?
  (empty-stack)
  (push (top any?) (tail Stack?))
)
(define (empty-stack? stack)
  (cases Stack stack
    (empty-stack () #t)
    (push (h t) #f))
)
(define (top stack)
  (cases Stack stack
    (empty-stack () (error 'top "accessing empty stack"))
    (push (h t) h)
  )
)
(define (pop stack)
  (cases Stack stack
    (empty-stack () (error 'pop "accessing empty stack"))
    (push (h t) t)
  )
)

; ex 2.23. identifier?
(define (identifier? ident)
  (and (symbol? ident) (not (equal? ident 'lambda)))
)

; ex 2.24. bintree-to-list
(define-datatype bintree bintree?
  (leaf-node (num integer?))
  (interior-node (key symbol?) (left bintree?) (right bintree?))
)

(define (bintree-to-list t)
  (cases bintree t
    (leaf-node (n) (list 'leaf-node n))
    (interior-node (k l r)
      (list 'interior-node k (bintree-to-list l) (bintree-to-list r)))
  )
)

; ex 2.25 max-interior
(define (max-interior root)
  (define (max-interior-impl max-info t)
    (cases bintree t
      (leaf-node (n) (values n max-info))
      (interior-node (k l r)
        (let*-values
          ( ((lsum lmax-info) (max-interior-impl max-info l))
            ((rsum rmax-info) (max-interior-impl lmax-info r))
            ((mid-sum) (+ lsum rsum)))
          (if (> mid-sum (cdr rmax-info))
            (values mid-sum (cons k mid-sum))
            (values mid-sum rmax-info))
        ))
    )
  )
  (let-values
    (((sum result)
      (max-interior-impl (cons 'no-interior-found -2147483648) root)))
    (car result)
  )
)

(define (list-of pred) (λ (l) (andmap pred l)))

; ex 2.26. red blue tree
(define-datatype RBTree RBTree?
  (rb-leaf (value integer?))
  (red-node  (left RBTree?) (right RBTree?))
  (blue-node (children (list-of RBTree?)))
)

(define (mark-leaves rbtree)
  (define (mark-leaves-impl depth t)
    (cases RBTree t
      (rb-leaf (v) (rb-leaf depth))
      (red-node (l r)
        (let ((new-depth (+ depth 1)))
          (red-node
            (mark-leaves-impl new-depth l)
            (mark-leaves-impl new-depth r))
        ))
      (blue-node (ns)
        (blue-node (map (λ (n) (mark-leaves-impl depth n))) ns))
    )
  )
  (mark-leaves-impl 0 rbtree)
)
