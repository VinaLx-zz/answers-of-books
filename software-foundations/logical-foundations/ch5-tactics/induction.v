Require Import Nat.
Require Import List.
Import ListNotations.

Theorem eqb_true : forall n m : nat,
  n =? m = true -> n = m.
Proof.
  induction n as [| n' IH].
  - intros. destruct m.
    + reflexivity.
    + simpl in H. discriminate H.
  - intros. destruct m.
    + simpl in H. discriminate H.
    + simpl in H. apply IH in H.
      rewrite H. reflexivity.
Qed.

(* The exercise may want us to induction on `list` to make use of generalize. *)
(* Luckily we can just induction on `n` and get away with it.                 *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intro n.
  induction n as [| n' IH].
  - intros. destruct l.
    + reflexivity.
    + simpl in H. discriminate H.
  - intros. destruct l.
    + reflexivity.
    + simpl in H. injection H. intro H'.
      apply IH in H'.
      simpl. apply H'.
Qed.
