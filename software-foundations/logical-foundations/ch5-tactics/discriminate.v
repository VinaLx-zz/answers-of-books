Require Import List.
Import ListNotations.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros. discriminate H.
Qed.
