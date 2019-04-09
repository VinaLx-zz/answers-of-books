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
    intros [| h1 t1] [| h2 t2] H;
    simpl in H;     (* unfold the split *)
    rewrite E in H; (* rewrite the induction to pair of list *)
    injection H; intros; (* then reason about pair equality *)
    try discriminate.
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
  destruct (f b) eqn: fbEq;
  destruct (f true) eqn: ftrue;
  destruct (f false) eqn: ffalse;
  try trivial;
  destruct b;
  try rewrite fbEq in ftrue;
  try rewrite fbEq in ffalse;
  try discriminate ftrue;
  try discriminate ffalse.
Qed.
