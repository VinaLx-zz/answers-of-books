#lang racket

(require "interpreter.rkt")
(require "type-checker.rkt")
(require "language.rkt")
(require "../eopl.rkt")

(define (run-program program) 
  (define/match (print-user-error user-error)
    (((exn:fail:user message _))
      (printf "~a\n" message)
    )
  )
  (with-handlers
    ((exn:fail:user? print-user-error))
    (define tp (type-of-program program))
    (printf "Type: ~v\n" tp)
    (value-of-program program)
  )
)

(define (run source)
  (define parse (sllgen:make-string-parser eopl:lex-spec modules-syntax))
  (run-program (parse source))
)

(define letrec-module-body "
module test
interface [
  even : (int -> int)
  odd  : (int -> int)
]
body letrec
  int e(n : int) =
    if zero?(n) then 1 else (o -(n, 1))
  int o(n : int) =
    if zero?(n) then 0 else (e -(n, 1))
in [
  even = e
  odd = o
]
(from test take even 10)
")

; (run letrec-module-body)

((sllgen:make-rep-loop "module> " run-program
   (sllgen:make-stream-parser eopl:lex-spec modules-syntax)))
