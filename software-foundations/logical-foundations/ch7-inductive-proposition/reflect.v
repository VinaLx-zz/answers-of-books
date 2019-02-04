Require Import Utf8.
Require Import Nat.
Require Import EqNat.
Require Import List.
Import ListNotations.

Inductive reflect (P : Prop) : bool → Prop :=
| ReflectT : P → reflect P true
| ReflectF : ¬ P → reflect P false.

Theorem reflect_iff : ∀ P b, reflect P b → (P ↔ b = true).
Proof.
  intros P b r. split; destruct r as [ref_true | ref_false].
  - intros. reflexivity.
  - intros. contradiction.
  - intros. assumption.
  - intro H. discriminate H.
Qed.

Theorem iff_reflect : ∀ P b, (P ↔ b = true) → reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. apply H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Lemma beq_natP : ∀ n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : ∀ n l,
  count n l = 0 → ~(In n l).
Proof.
  intros n l. induction l as [| h t IH].
  - intros count_n_nil_0 in_n_nil.
    simpl in in_n_nil. contradiction.
  - simpl. intros count_n_ht_0 in_n_ht.
    destruct (beq_natP n h) as [n_eq_h | n_n_eq_h].
    + simpl in count_n_ht_0. discriminate count_n_ht_0.
    + simpl in count_n_ht_0. apply IH in count_n_ht_0.
      destruct in_n_ht.
        * symmetry in H. contradiction.
        * contradiction.
Qed.

