#lang racket/base

(provide (all-defined-out))

; ex 1.7. informative error message for nth-element
(define (nth-element l n)
  (define (nth-element-impl cl cn)
    (cond
      ((null? cl)
        (error 'nth-element "~a doesn't have ~a elements" l (+ n 1)))
      ((equal? cn 0) (car cl))
      (else (nth-element-impl (cdr cl) (- cn 1)))
    )
  )
  (nth-element-impl l n)
)

; ex 1.9.
(define (remove e l)
  (cond
    ((null? l) null)
    ((equal? (car l) e) (remove e (cdr l)))
    (else (cons (car l) (remove e (cdr l))))
  )
)

; ex 1.12. inlined subst
(define (subst new old slist)
  (if (null? slist) null
    (let* (
      (h (car slist))
      (t (cdr slist))
      (new-h
        (cond
          ((list? h) (subst new old h))
          ((equal? old h) new)
          (else h)
        )
      ))
      (cons new-h (subst new old t))
    ) ; let
  ) ; if
)

; ex 1.13. subst with map
(define (subst2 new old slist)
  (map (λ (sexpr) (subst-s-expr new old sexpr)) slist)
)

(define (subst-s-expr new old sexpr)
  (cond
    ((list? sexpr) (subst2 new old sexpr))
    ((equal? sexpr old) new)
    (else sexpr)
  )
)

; ex 1.15. duple
(define (duple n x)
  (if (equal? n 0) null
    (cons x (duple (- n 1) x))))

; ex 1.16. invert
(define (invert l)
  (define (swap l) (list (cadr l) (car l)))
  (map swap l)
)

; ex 1.17. down
(define (down l) (map list l))

; ex 1.18. swapper
(define (map-slist f slist)
  (if (list? slist)
    (map (λ (e) (map-slist f e)) slist)
    (f slist)
  )
)

(define (swapper a b slist)
  (define (try-swap e)
    (cond
      ((equal? e b) a)
      ((equal? e a) b)
      (else e)))
  (map-slist try-swap slist)
)

; ex 1.19. list-set
(define (list-set xs n x)
  (cond
    ((null? xs) null)
    ((equal? n 0) (cons x (cdr xs)))
    (else (cons (car xs) (list-set (cdr xs) (- n 1) x)))
  )
)

; ex 1.20. count-occurrences
(define (foldr-slist f z slist)
  (if (list? slist)
    (foldr
      (λ (sl acc) (foldr-slist f acc sl)) z slist)
    (f slist z)
  )
)

(define (count-occurrences x slist)
  (foldr-slist
    (λ (e acc) (if (equal? e x) (+ 1 acc) acc))
    0 slist)
)

; ex 1.21. product
(define (product xs ys)
  (define (pair-with x xs) (map (λ (y) (list x y)) xs))
  (if (null? xs) null
    (append
      (pair-with (car xs) ys)
      (product   (cdr xs) ys))
  )
)

; ex 1.22. filter
(define (filter-in p xs)
  (foldr (λ (x acc) (if (p x) (cons x acc) acc)) null xs)
)

; ex 1.23. list-index
(define (list-index p xs)
  (define (list-index-from n p xs)
    (cond
      ((null? xs) #f)
      ((p (car xs)) n)
      (else (list-index-from (+ n 1) p (cdr xs)))
    )
  )
  (list-index-from 0 p xs)
)

; ex 1.24. every
(define (every p xs)
  (equal?
    (list-index (λ (x) (not (p x))) xs) 
    #f
  )
)

; ex 1.25. exists
(define (exists p xs)
  (not (equal? (list-index p xs) #f))
)

; ex 1.26. up
(define (up xs)
  (foldr
    (λ (x acc)
      (if (list? x) (append x acc) (cons x acc)))
    null xs
  )
)

; ex 1.27. flatten
(define (flatten slist) (foldr-slist cons null slist))

; ex 1.28. merge
(define (merge/predicate p xs ys)
  (cond
    ((null? xs) ys)
    ((null? ys) xs)
    (else
      (let ((hx (car xs)) (tx (cdr xs))
            (hy (car ys)) (ty (cdr ys)))
        (if (p hx hy)
          (cons hx (merge/predicate p tx ys))
          (cons hy (merge/predicate p xs ty))
        )
      ) ; let
    ) ; else
  ) ; cond
)

(define (merge xs ys) (merge/predicate < xs ys))

; ex 1.30. sort/predicate
(define (split-at xs n)
  (cond
    ((equal? 0 n) (values null xs))
    ((null? xs) (values xs null))
    (else
      (let-values
        (((xs1 xs2) (split-at (cdr xs) (- n 1))))
        (values (cons (car xs) xs1) xs2)
      )
    )
  ) ; cond
)

(define (sort/predicate p xs)
  (let ((l (length xs)))
    (if (<= l 1) xs
      (let-values
        (((xs1 xs2) (split-at xs (quotient l 2))))
        (printf "~a ~a\n" xs1 xs2)
        (merge/predicate
          p (sort/predicate p xs1) (sort/predicate p xs2))
      )
    ) ; if
  ) ; let
)

; ex 1.29. sort

(define (sort xs) (sort/predicate < xs))

; ex 1.31. binary tree abstraction

(define (interior-node c l r) (list 'node c l r))
(define (iterior-node? t) (equal? (car t) 'node))
(define (leaf v) (list 'leaf v))
(define (leaf? t) (equal? (car t) 'leaf))
(define lson caddr)
(define rson cadddr)
(define contents-of cadr)

; 1.32. double-tree

(define (double-tree t)
  (if (leaf? t)
    (leaf (* (contents-of t) 2))
    (interior-node
      (contents-of t)
      (double-tree (lson t))
      (double-tree (rson t))
    )
  )
)

; 1.33. mark-leaves-with-red-depth

(define (mark-leaves-with-red-depth t)
  (define (mark-leaves-with-current-red-depth d t)
    (if (leaf? t) (leaf d)
      (let
        ((next-depth (if (equal? (contents-of t) 'red) (+ d 1) d)))
        (interior-node
          (contents-of t)
          (mark-leaves-with-current-red-depth next-depth (lson t))
          (mark-leaves-with-current-red-depth next-depth (rson t))
        )
      )
    )
  ) ; mark-leaves-with-current-red-depth
  (mark-leaves-with-current-red-depth 0 t)
)

; 1.34. path of binary search tree (use a different representation from above)

(define (path a t)
  (cond
    ((null? t) null)
    ((equal? (car t) a) null)
    ((< (car t) a)
      (cons 'right (path a (caddr t))))
    (else
      (cons 'left  (path a (cadr t))))
  )
)

; 1.35. number-leaves

(define (number-leaves t)
  (define (number-leaves-from n t)
    (if (leaf? t)
      (values (leaf n) (+ n 1))
      (let*-values
        (((left  n1) (number-leaves-from n  (lson t)))
         ((right n2) (number-leaves-from n1 (rson t)))
        )
        (values (interior-node (contents-of t) left right) n2)
      )
    )
  )
  (let-values (((result n) (number-leaves-from 0 t))) result)
)

; 1.36. find a 'g' that completes 'number-elements2'
(define (number-elements2 lst)
  ; this is exercise
  (define (g h t)
    (define (increment-index p) (list (+ 1 (car p)) (cadr p)))
    (cons h (map increment-index t))
  )
  ; this is given
  (if (null? lst) null
    (g (list 0 (car lst)) (number-elements2 (cdr lst)))))
