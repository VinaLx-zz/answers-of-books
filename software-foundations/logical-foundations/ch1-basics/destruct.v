Require Import Coq.Init.Nat.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + discriminate.
  - destruct c.
    + reflexivity.
    + discriminate.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity. 
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f p b.
  rewrite -> (p b).
  rewrite -> (p b).
  reflexivity.
Qed.

Theorem identity_negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f p b.
  rewrite -> (p b).
  rewrite -> (p (negb b)).
  destruct b.
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b.
    - destruct c.
      + reflexivity.
      + discriminate.
    - destruct c.
      + discriminate.
      + reflexivity.
Qed.

