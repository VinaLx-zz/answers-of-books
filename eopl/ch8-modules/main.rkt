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

(define opaque-type-module "
module nat
interface [
  opaque N
  z    : N
  succ : (N -> N)
  pred : (N -> N)
  isZ  : (N -> bool)
]
body [
  type N = int
  z    = 0
  succ = proc(n1: N) -(n1, -1)
  pred = proc(n2: N) -(n2, 1)
  isZ  = proc(n3: N) zero?(n3)
]
letrec
int ntoi(n4 : from nat take N) =
  if (from nat take isZ n4)
    then 0
    else -((ntoi (from nat take pred n4)), -1)
in letrec
from nat take N iton(n5: int) =
  if zero?(n5)
    then from nat take z
    else (from nat take succ (iton -(n5, 1)))
in
  (ntoi (iton 10))
")

(define module-proc "
interface natinterf = [
  opaque N
  z    : N
  succ : (N -> N)
  pred : (N -> N)
  isZ  : (N -> bool)
]
module nat
interface
  natinterf
body [
  type N = int
  z    = 0
  succ = proc(n1: N) -(n1, -1)
  pred = proc(n2: N) -(n2, 1)
  isZ  = proc(n3: N) zero?(n3)
]
module intnatp
interface (n : natinterf) => [
  intToNat : (int -> from n take N)
  natToInt : (from n take N -> int)
]
body
  module-proc (nn : natinterf)
  letrec
  int ntoi(x : from nn take N) =
    if (from nn take isZ x)
      then 0
      else -((ntoi (from nn take pred x)), -1)
  in letrec
  from nn take N iton(y : int) =
    if zero?(y)
      then from nn take z
      else (from nn take succ (iton -(y, 1)))
  in [
    intToNat = iton
    natToInt = ntoi
  ]
module intnat
interface [
  intToNat : (int -> from nat take N)
  natToInt : (from nat take N -> int)
]
body (intnatp nat)
(from intnat take natToInt (from intnat take intToNat 10))
")

(run module-proc)

; ((sllgen:make-rep-loop "module> " run-program
   ; (sllgen:make-stream-parser eopl:lex-spec modules-syntax)))
