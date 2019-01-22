Require Import Nat.
Require Import List.
Import ListNotations.

Inductive TwoStepNat : nat -> Type :=
| end_in_zero : TwoStepNat 0
| end_in_one : TwoStepNat 1
| two_step : forall {n' : nat}, TwoStepNat n' -> TwoStepNat (S (S n')).

Fixpoint nat_two_step (n : nat) : TwoStepNat n :=
  match n with
  | 0 => end_in_zero
  | S 0 => end_in_one
  | S (S n') => two_step (nat_two_step n')
  end.

Theorem odd_s_even : forall n : nat,
  odd n = true -> even (S n) = true.
Proof.
  intros.
  induction (nat_two_step n).
  - simpl in H. discriminate.
  - reflexivity.
  - apply IHt. apply H.
Qed.

(* I don't really understand this exercise so I just prove it myself... *)
Theorem silly_ex :
  (forall n, even n = true -> odd (S n) = true) ->
  odd 3 = true -> even 4 = true.
Proof.
  intro. apply odd_s_even.
Qed.

(* These are proved in chapter 3, just use axiom to avoid too many copy *)
Axiom rev_involutive : forall l : list nat, (rev (rev l)) = l.

Axiom rev_inject : forall l1 l2 : list nat,
  rev l1 = rev l2 -> l1 = l2.

Theorem rev_exercise1 : forall l l' : list nat,
   l = rev l' -> l' = rev l.
Proof.
  intros.
  apply rev_inject.
  rewrite rev_involutive.
  symmetry.
  apply H.
Qed.

(* apply with *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite eq1. rewrite eq2.
  reflexivity.
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
  | 0 => 0
  | (S 0) => 0
  | (S (S n')) => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with m.
  - apply H0.
  - apply H.
Qed.

