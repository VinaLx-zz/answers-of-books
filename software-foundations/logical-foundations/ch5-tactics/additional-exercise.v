Require Import EqNat.
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Datatypes.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  induction n as [| n' IH];
  intros [| m']; try reflexivity.
  simpl. apply IH.
Qed.

Theorem eqb_true_eq : forall n m : nat,
  n = m -> n =? m = true.
Proof.
  induction n as [| n' IH]; intros [| m']; intros.
  - reflexivity.
  - simpl in H. discriminate H.
  - simpl in H. discriminate H.
  - injection H. intros. apply IH in H0. simpl. apply H0.
Qed.

Theorem eqb_trans : forall n m p : nat,
  n =? m = true -> m =? p = true -> n =? p = true.
Proof.
  intros.
  apply beq_nat_true in H.
  apply beq_nat_true in H0.
  rewrite H. rewrite H0.
  apply eqb_true_eq. reflexivity.
Qed.

Definition split_combine_statement : Prop :=
  forall (X : Type) (xs : list X) (Y: Type) (ys : list Y),
  length xs = length ys -> split (combine xs ys) = (xs, ys).

Theorem split_combine : split_combine_statement.
Proof.
  intros until xs. induction xs as [| x xs' IH]
  ;intros ;destruct ys as [| y ys'] ;simpl in H.
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - injection H. intros H'. simpl.
    apply IH in H'. rewrite H'. reflexivity.
Qed.

Theorem filter_exercise :
  forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros until l.
  generalize dependent x. generalize dependent test.
  induction l as [| h t IH]; intros; try destruct (test h) eqn: E; simpl in H.
  - discriminate H.
  - rewrite E in H.
    injection H. intros.
    rewrite <- H1. assumption.
  - rewrite E in H. apply IH in H.
    assumption.
Qed.

Definition forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  fold_right (fun x b => andb (test x) b) true l.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Definition existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  fold_right (fun x b => orb (test x) b) false l.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros.
  generalize dependent test. induction l as [| h t IH]; intros.
  - unfold existsb'. reflexivity.
  - unfold existsb'. destruct (test h) eqn: E;
    simpl; rewrite E; simpl.
    + reflexivity.
    + unfold existsb in IH. unfold existsb' in IH.
      unfold existsb. apply IH.
Qed.

