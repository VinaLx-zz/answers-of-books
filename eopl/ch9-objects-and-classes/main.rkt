#lang racket

(require "data.rkt")
(require "interpreter.rkt")
(require "language.rkt")
(require "../eopl.rkt")

(define (run-program program) 
  (define/match (print-user-error user-error)
    (((exn:fail:user message _)) (printf "~a\n" message))
  )
  (with-handlers
    ((exn:fail:user? print-user-error))
    ; (define tp (type-of-program program))
    ; (printf "Type: ~v\n" tp)
    (expval->val (value-of-program program))
  )
)

(define (run source)
  (define parse (sllgen:make-string-parser eopl:lex-spec oo-syntax))
  (run-program (parse source))
)

(define dynamic-and-super "
class c1 extends object
  method public int initialize () 1
  method public int m1 () send self m2()
  method public int m2 () 13
class c2 extends c1
  method public int m1 () 22
  method public int m2 () 23
  method public int m3 () super m1()
class c3 extends c2
  method public int m1 () 32
  method public int m2 () 33
let o3 = new c3()
in  send o3 m3()
")

(define inheritance "
class point extends object
  field private int x
  field private int y
  method public unit initialize (initx : int, inity : int)
  begin set x = initx
      ; set y = inity
  end
  method public unit move (dx : int, dy : int)
  begin set x = +(x,dx)
      ; set y = +(y,dy)
  end
  method public list int get-location () list(x,y)

class colorpoint extends point
  field private int color
  method public unit set-color (c : int) set color = c
  method public int get-color () color

let p  = new point(3,4)
    cp = new colorpoint(10,20)
in
begin send p move(3,4)
    ; send cp set-color(87)
    ; send cp move(10,20)
    ; list(send p get-location(),
           send cp get-location(),
           send cp get-color())
end
")

(run dynamic-and-super)
(run inheritance)

; ((sllgen:make-rep-loop "oo> " run-program
   ; (sllgen:make-stream-parser eopl:lex-spec oo-syntax)))
