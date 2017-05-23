#lang racket

(provide derivative)

(define (derivative expression var)
 (cond ((number? expression) 0)
       ((variable? expression) (if (same-variable? expression var) 1 0))
       ((sum? expression) (make-sum (derivative (addend expression) var)
                                    (derivative (augend expression) var)))
       ((product? expression)
         (let ((lhs (multiplier expression))
               (rhs (multiplicant expression)))
           (make-sum (make-product lhs (derivative rhs var))
                     (make-product rhs (derivative lhs var)))))
       ((exponent? expression)
         (let ((b (base expression))
               (e (exponent expression)))
           (make-product
             (make-product e (make-exp b (make-sum e -1)))
             (derivative b var))))
       (else (error 'derivative "unknown expression type"))))

(define (=number? expression num) (and (number? expression) (= expression num)))
(define variable? symbol?)
(define (same-variable? x y)
  (and (variable? x) (variable? y) (eq? x y)))

(define (make-sum x y)
  (cond ((=number? x 0) y)
        ((=number? y 0) x)
        ((and (number? x) (number? y)) (+ x y))
        (else (list '+ x y))))

(define (make-product x y)
  (cond ((=number? x 1) y)
        ((=number? y 1) x)
        ((or (=number? x 0) (=number? y 0)) 0)
        ((and (number? x) (number? y) (* x y)))
        (else (list '* x y))))

(define (make-exp x y)
  (cond ((or (=number? x 1) (=number? y 0)) 1)
        ((or (=number? y 1) (=number? x 0)) x)
        ((and (number? x) (number? y) (expt x y)))
        (else (list '** x y))))

(define ((binary-op? op) expression)
  (and (pair? (rest expression)) (eq? (first expression) op)))

(define sum? (binary-op? '+))
(define product? (binary-op? '*))
(define exponent? (binary-op? '**))

(define addend cadr)
(define augend caddr)
(define multiplicant cadr)
(define multiplier caddr)
(define base cadr)
(define exponent caddr)
