#lang racket

(provide (all-defined-out))

; ex 2.15. ex 2.16.
;   lambda expression representation

(module lambda-exp racket
  (provide (all-defined-out))

  (define (make-data-predicate label)
  (λ (data) (equal? (car data) label))
  )

  (define (var-exp var) (list 'var-exp))
  (define var-exp? (make-data-predicate 'var-exp))
  (define var-exp->var cadr)

  (define (lambda-exp var expr) (list 'lambda-exp var expr))
  (define lambda-exp? (make-data-predicate 'lambda-exp))
  (define lambda-exp->bound-var cadr)
  (define lambda-exp->body caddr)

  (define (app-exp op arg) (list 'app-exp op arg))
  (define app-exp? (make-data-predicate 'app-exp))
  (define app-exp->rator cadr)
  (define app-exp->rand caddr)
)

; ex 2.18 sequence

(module sequence racket
  (provide (all-defined-out))
  (define (number->sequence n) (list n null null))
  (define current-element car)
      
  (define seq->left cadr)
  (define seq->right caddr)
  (define (move-to-left seq)
  (if (null? (seq->left seq)) (error 'move-to-left "fail with ~a" seq)
      (list
      (car (seq->left seq))
      (cdr (seq->left seq))
      (cons current-element (seq->right seq))
      )
  )
  )
  (define (move-to-right seq)
  (if (null? (seq->right seq)) (error 'move-to-right "fail with ~a" seq)
      (list
      (car (seq->right seq))
      (cons (current-element seq) (seq->left seq))
      (cdr (seq->right seq))
      )
  )
  )
  (define (insert-to-left n seq)
  (list
      (current-element seq)
      (cons n (seq->left seq))
      (seq->right seq)
  )
  )
  (define (insert-to-right n seq)
  (list
      (current-element seq)
      (seq->left seq)
      (cons n (seq->right seq)))
)

)
; ex 2.19. ex 2.20. binary tree

(module bintree racket
  (define (make-tree e parents children)
    (list e parents children)
  )
  (define empty-tree (make-tree null null null))
  (define (number->bintree n) (make-tree n null (cons null null)))
  (define current-element car)
  (define parents cadr)
  (define children caddr)
  (define left-child (compose car children))
  (define right-child (compose cdr children))

  (define at-leaf? (compose null? current-element))
  (define at-root? (compose null? parents))
  (define move-up (compose car parents))

  (define (move-to-left t)
    (let ((next    (left-child t))
          (l-parents (cons t (parents t))))
      (make-tree next l-parents (children next))
    )
  )
  (define (move-to-right t)
    (let ((next    (right-child t))
          (r-parents (cons t (parents t))))
      (make-tree next r-parents (children next))
    )
  )
  (define (insert-to-left n t)
    (let* ((l-parents (cons t (parents t)))
           (l-left-child (left-child t))
           (l (list n l-parents (cons l-left-child null))))
      (make-tree (current-element t) (parents t) (cons l (right-child t)))
    )
  )
  (define (insert-to-right n t)
    (let* ((r-parents (cons t (parents t)))
           (r-right-child (right-child t))
           (r (list n r-parents (cons null r-right-child))))
      (make-tree (current-element t) (parents t) (cons (left-child t) r))
    )
  )
)

