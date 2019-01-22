Require Import List.
Import ListNotations.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros until l.
  induction l as [| h t IH].
  - intros [| h1 t1] [| h2 t2] H.
    all: simpl. all: try reflexivity.
    + simpl in H. injection H. intros. discriminate H0.
  - destruct h as [hx hy].
    destruct (split t) as [tx ty] eqn: E.
    intros [| h1 t1] [| h2 t2] H.
    all: simpl in H.     (* unfold the split *)
    all: rewrite E in H. (* rewrite the induction to pair of list *)
    all: injection H. all: intros. (* then reason about pair equality *)
    + discriminate H0.
    + discriminate H2.
    + discriminate H0.
    + assert (I : (tx, ty) = (t1, t2)).
        rewrite H0. rewrite H2. reflexivity.
      simpl. rewrite H1. rewrite H3.
      apply IH in I. rewrite I.
      reflexivity.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool), f (f (f b)) = f b.
Proof.
  intros.
  destruct (f b) eqn: fbEq.
  all: destruct (f true) eqn: ftrue.
  all: destruct (f false) eqn: ffalse.
  all: try trivial.
  all: destruct b.
  all: try rewrite fbEq in ftrue.
  all: try rewrite fbEq in ffalse.
  all: try discriminate ftrue.
  all: try discriminate ffalse.
Qed.
