Require Import List.
Import ListNotations.

Fixpoint split {X Y : Type} (l : list (X * Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => let (xs, ys) := split t in (x :: xs, y :: ys)
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

