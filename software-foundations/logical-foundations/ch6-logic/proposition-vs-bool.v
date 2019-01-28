Require Import Nat.

Inductive DoubleStep : nat -> Type :=
  | d_zero : DoubleStep 0
  | d_one : DoubleStep 1
  | d_step : forall {n : nat}, DoubleStep n -> DoubleStep (S (S n))
.

Fixpoint double_step (n : nat) : DoubleStep n :=
    match n with
    | 0 => d_zero
    | S 0 => d_one
    | (S (S n')) => d_step (double_step n')
    end.

(* since the implementation of `double` is quite different in standard library *)
(* and software foundation. In standard library `double n = n + n` instead of a*)
(* recursive definition, so the proof involving `double` would be more complex *)
Theorem even_double_conv : forall n : nat,
  exists k, n = if even n then double k
                else S (double k).
Proof.
  intros n. destruct (even n) eqn: E.
  - induction (double_step n). 
    + exists 0. reflexivity.
    + simpl in E. discriminate E.
    + simpl in E. apply IHd in E. destruct E as [k' ndoublek'].
      unfold double in ndoublek'.
      exists (S k'). unfold double. rewrite <- plus_n_Sm. simpl.
      rewrite ndoublek'. reflexivity.
  - induction (double_step n).
    + simpl in E. discriminate E.
    + exists 0. reflexivity.
    + simpl in E. apply IHd in E. destruct E as [k' nsdoublek'].
      unfold double in nsdoublek'.
      exists (S k'). unfold double. rewrite <- plus_n_Sm. simpl.
      rewrite nsdoublek'. reflexivity.
Qed.

Theorem even_bool_prop : forall n : nat,
  even n = true <-> exists k, n = double k.
Proof.
  intro n. split; intros.
  - destruct (even_double_conv n) as [k ndoublek].
    rewrite H in ndoublek. exists k. apply ndoublek.
  - destruct H as [k ndoublek].
    generalize dependent n.
    induction k as [| k'].
    + intros. rewrite ndoublek. reflexivity.
    + intros.
      unfold double in ndoublek. unfold double in IHk'.
      rewrite <- plus_n_Sm in ndoublek. simpl in ndoublek.
      assert (exists n', n = S (S n') /\ n' = k' + k') as H.
      exists (k' + k'). split. apply ndoublek. reflexivity.
      destruct H as [n' [ssn'n n'k'k']].
      apply IHk' in n'k'k'.
      rewrite ssn'n. simpl. apply n'k'k'.
Qed.

Require Import Bool.

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split; intros.
  - destruct b1; destruct b2; split; solve [reflexivity | discriminate H].
  - destruct H. rewrite H. rewrite H0. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split; intros.
  - destruct b1.
    + left. reflexivity.
    + destruct b2.
      * right. reflexivity.
      * simpl in H. discriminate H.
  - destruct H as [b1t | b2t].
    + rewrite b1t. reflexivity.
    + rewrite b2t. destruct b1; reflexivity.
Qed.

Require EqNat.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split; intros.
  - apply EqNat.beq_nat_false. apply H.
  - destruct (x =? y) eqn: xyt.
    + symmetry in xyt. apply EqNat.beq_nat_eq in xyt.
      contradiction.
    + reflexivity.
Qed.

Require Import List.
Import ListNotations.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | h1 :: t1, h2 :: t2 => eqb h1 h2 && eqb_list eqb t1 t2
  end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros until l1.
  induction l1 as [| h t IH]; split; intros.
  - destruct l2; simpl in H0. reflexivity. discriminate H0.
  - destruct l2. reflexivity. discriminate H0.
  - destruct l2; simpl in H0.
    + discriminate H0.
    + apply andb_true_iff in H0. destruct H0 as [heq teq].
      apply H in heq. apply IH in teq.
      rewrite heq. rewrite teq. reflexivity.
  - destruct l2; simpl.
    + discriminate H0.
    + injection H0. intros teq heq. apply H in heq. apply IH in teq.
      rewrite heq. rewrite teq. reflexivity.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Theorem forallb_true_iff : forall (X : Type) (test : X -> bool) (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros. split; induction l as [| h t IH]; intros.
  - simpl. apply I.
  - simpl in H. apply andb_true_iff in H as [ht tt].
    simpl. apply IH in tt. apply (conj ht tt).
  - reflexivity.
  - simpl in H. destruct H as [ht tt]. apply IH in tt.
    simpl. rewrite ht. rewrite tt. reflexivity.
Qed.
