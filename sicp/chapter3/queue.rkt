#lang racket

(provide (all-defined-out))

(define front-ptr mcar)
(define rear-ptr mcdr)

(define set-front-ptr! set-mcar!)
(define set-rear-ptr! set-mcdr!)

(define (empty-queue? q) (null? (front-ptr q)))

(define (empty-queue) (mcons empty empty))

(define (front-queue q)
  (if (empty-queue? q) (error `front-queue "require an non-empty queue")
    (mcar (front-ptr q))))

(define (rear-queue q)
  (if (empty-queue? q) (error `rear-queue "require an non-empty queue")
    (mcar (rear-ptr q))))

(define (front-insert-queue! q x)
  (let ((new-pair (mcons x empty)))
    (if (empty-queue? q)
      (set-front-ptr! q new-pair)
      (set-mcdr! (rear-ptr q) new-pair))
    (set-rear-ptr! q new-pair)
    q))

(define (rear-insert-queue! q x)
  (if (empty-queue? q) (front-insert-queue! q x)
    (let ((new-pair (mcons x empty)))
      (set-mcdr! (rear-ptr q) new-pair)
      (set-rear-ptr! q new-pair)
      q)))

(define (front-delete-queue! q)
  (if (empty-queue? q) (error `delete-queue "require an non-empty queue")
    (begin (set-front-ptr! q (mcdr (front-ptr q)))
           (if (empty-queue? q) (set-rear-ptr! q empty) (void))
           q)))

(define (print-queue q)
  (define (print-queue-impl l)
    (if (empty? l) (printf ")\n")
      (begin (printf " ~a" (mcar l))
      (print-queue-impl (mcdr l)))))
  (if (empty-queue? q) (printf "()\n")
    (begin (printf "(~a" (front-queue q))
           (print-queue-impl (mcdr (front-ptr q))))))
