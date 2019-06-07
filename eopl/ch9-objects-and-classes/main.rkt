#lang racket

(require "data.rkt")
(require "interpreter.rkt")
(require "language.rkt")
(require "type-checker.rkt")
(require "../eopl.rkt")

(define (run-program program) 
  (define/match (print-user-error user-error)
    (((exn:fail:user message _)) (printf "~a\n" message))
  )
  (with-handlers
    ((exn:fail:user? print-user-error))
    (define tp (type-of-program program))
    (printf "Type: ~v\n" tp)
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
           list(send cp get-color()))
end
")

(define tree "
interface tree
  method int  sum()
  method bool equal(t: tree)

class branch extends object implements tree
  field private tree left
  field private tree right
  method public unit initialize(l: tree, r: tree)
    begin set left = l; set right = r end
  method public tree getleft () left
  method public tree getright () right
  method public int sum() +(send left sum(), send right sum())
  method public bool equal(t: tree)
    if instance-of t branch
    then if send left equal(send cast t branch getleft())
         then send right equal(send cast t branch getright())
         else zero?(1)
    else zero?(1)

class leaf extends object implements tree
  field private int value
  method public unit initialize(v: int) set value = v
  method public int sum() value
  method public int getvalue() value
  method public bool equal(t : tree)
    if instance-of t leaf
    then zero?(-(value, send cast t leaf getvalue()))
    else zero?(1)

let t = new branch(new branch(new leaf(3), new leaf(4)), new leaf(5))
in  list(send t sum(), if send t equal(t) then 1 else 0)
")

(run dynamic-and-super)
(run inheritance)
(run tree)

; ((sllgen:make-rep-loop "oo> " run-program
   ; (sllgen:make-stream-parser eopl:lex-spec oo-syntax)))
