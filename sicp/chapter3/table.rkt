#lang racket

(provide (all-defined-out))

(define (massoc key table)
  (cond ((empty? table) false)
        ((equal? key (mcar (mcar table))) (mcar table))
        (else (massoc key (mcdr table)))))

(define (lookup key table)
  (let ((record (massoc key (mcdr table))))
    (if record (mcdr record) false)))

(define (insert! table key value)
  (let ((record (massoc key (mcdr table))))
    (if record (set-mcdr! record value)
      (set-mcdr! table (mcons (mcons key value) (mcdr table))))))

(define (empty-table) (mcons 'table empty))
