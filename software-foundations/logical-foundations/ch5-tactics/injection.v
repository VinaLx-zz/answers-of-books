Require Import List.
Import ListNotations.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
Proof.
  intros.
  injection H0. intros. symmetry. assumption.
Qed.

