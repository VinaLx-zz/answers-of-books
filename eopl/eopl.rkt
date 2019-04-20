#lang racket

(provide (all-defined-out))

(require
  (only-in eopl
    sllgen:make-string-parser
    sllgen:make-stream-parser
    sllgen:make-define-datatypes
    sllgen:make-rep-loop
    list-of
    define-datatype
    cases
    (define sllgen:define)))

(provide (all-from-out eopl))

(sllgen:define eopl:lex-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
  )
)

(define (cons-of p1 p2)
  (λ (c)
    (and (cons? c) (p1 (car c)) (p2 (cdr c)))
  )
)
