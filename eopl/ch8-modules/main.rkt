#lang racket

(require "interpreter.rkt")
(require "type-checker.rkt")
(require "language.rkt")
(require "../eopl.rkt")

(define (run program) 
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

((sllgen:make-rep-loop "module> " run
   (sllgen:make-stream-parser eopl:lex-spec modules-syntax)))
