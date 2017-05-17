#lang racket

(provide (all-defined-out))

(define (make-interval a b)
  (if (< a b) (cons a b) (cons b a)))

(define lower-bound car)
(define upper-bound cdr)

(define (make-center-width c w)
  (make-interval (- c w) (+ c w)))

(define (make-center-percent c p)
  (make-center-width c (* c p)))

(define (center i)
  (/ (+ (upper-bound i) (lower-bound i)) 2))

(define (width i)
  (/ (- (upper-bound i) (lower-bound i)) 2))

(define (uncertainty i) (/ (width i) (center i)))

(define (show-interval i)
  (printf "~a - ~a\n" (lower-bound i) (upper-bound i)))

(define (negative-interval i)
  (make-interval (- (upper-bound i)) (- (lower-bound i))))

(define (add-interval x y)
  (make-interval (+ (lower-bound x) (lower-bound y))
                 (+ (upper-bound x) (upper-bound y))))

(define (sub-interval x y)
  (add-interval x (negative-interval y)))

(define (mul-interval x y)
  (let ((lx (lower-bound x))
        (ly (lower-bound y))
        (ux (upper-bound x))
        (uy (upper-bound y)))
    (cond ((and (>= lx 0) (>= ly 0)) (make-interval (* lx ly) (* ux uy)))
          ((and (<= ux 0) (<= uy 0)) (make-interval (* ux uy) (* lx ly)))
          ((and (>= lx 0) (<= uy 0)) (make-interval (* lx uy) (* ux ly)))
          ((and (<= ux 0) (>= ly 0)) (make-interval (* ux ly) (* lx uy)))
          ((>= lx 0) (make-interval (* ux ly) (* ux uy)))
          ((>= ly 0) (make-interval (* uy lx) (* uy ux)))
          ((<= ux 0) (make-interval (* lx uy) (* lx ly)))
          ((<= uy 0) (make-interval (* ly ux) (* ly lx)))
          (else (make-interval (min (* lx uy) (* ly ux))
                               (max (* lx ly) (* ux uy)))))))

(define (div-interval x y)
  (if (and (<= (lower-bound y) 0) (>= (upper-bound y) 0))
    (error 'div-interval "cannot divide an interval spanning 0")
    (mul-interval x (make-interval
      (/ 1.0 (upper-bound y)) (/ 1.0 (lower-bound y))))))

(define one (make-interval 1 1))

(define (par1 x y)
  (div-interval (mul-interval x y) (add-interval x y)))

(define (par2 x y)
  (div-interval one (add-interval (div-interval one x) (div-interval one y))))

; since fraction of interval cannot be reduced
; so interval arithmetic is different from plain number

