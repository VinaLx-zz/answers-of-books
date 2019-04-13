#lang racket

(provide (all-defined-out))

; ex 2.1. big ints
(module big-int racket
  (provide (all-defined-out))

  (define radix 16)

  (define zero null)
  (define is-zero? null?)
  (define (successor n)
    (if (null? n) (list 1)
      (let ((new-lowest (+ 1 (car n))))
        (if (equal? new-lowest radix)
          (cons 0 (successor (cdr n)))
          (cons new-lowest (cdr n))
        )
      )
    )
  )
  (define (predecessor n)
    (define (is-one? n) (equal? n (list 1)))
    (if (null? n)
      (error 'predecessor "zero has no predecessor")
      (if (equal? (car n) 0)
        (cons (- radix 1) (predecessor (cdr n)))
        (if (is-one? n) zero
          (cons (- (car n) 1) (cdr n))
        )
      )
    )
  )
  (define (plus m n)
    (if (is-zero? m) n
      (successor (plus (predecessor m) n))
    )
  )
  (define (mult m n)
    (if (is-zero? m) zero
      (plus n (mult (predecessor m) n))
    )
  )
  (define (factorial n)
    (if (is-zero? n) (successor zero)
      (mult n (factorial (predecessor n)))
    )
  )
  (define (to-number n)
    (if (is-zero? n) 0
      (+ (car n) (* radix (to-number (cdr n))))
    )
  )
  (define (from-number n)
    (if (equal? n 0) zero
      (let-values
        ( ((q r) (quotient/remainder n radix)) )
        (cons r (from-number q))
      )
    )
  )
)

(require (prefix-in big: 'big-int))
(provide (all-from-out 'big-int))

; ex 2.3. diff tree representation of number
(module diff-tree racket
  (provide (all-defined-out))

  (struct diff (l r) #:transparent)
  (struct one () #:transparent)

  (define zero (diff (one) (one)))

  (define (to-number n)
    (match n
      ((one) 1)
      ((diff l r) (- (to-number l) (to-number r)))
    )
  )
  (define (is-zero? n) (equal? (to-number n) 0))

  (define minus-one (diff zero (one)))
  (define (successor n) (diff n minus-one))
  (define (predecessor n) (diff n (one)))
  (define (minus n)
    (match n
      ((one) minus-one)
      ((diff l r) (diff r l))
    )
  )
  (define (diff-tree-plus m n) (diff m (minus n)))
)

(require (prefix-in dt: 'diff-tree))
(provide (all-from-out 'diff-tree))
