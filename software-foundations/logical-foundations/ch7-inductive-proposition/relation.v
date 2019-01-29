Require Import Peano.
Require Import Utf8.
Require Import PeanoNat.
Import Nat.

Inductive total_relation : nat -> Prop :=
  | any_num : forall n : nat, total_relation n
.

Inductive empty_relation : nat -> Prop :=
.

Theorem le_loose : ∀ m n, S m ≤ n → m ≤ n.
Proof.
  intros m n sm_le_n.
  induction sm_le_n as [| pn sm_le_pn IH].
  - apply le_S. apply le_n.
  - apply le_S. apply IH.
Qed.

Lemma le_trans : ∀ m n o : nat, m ≤ n → n ≤ o → m ≤ o.
Proof.
  intros m n o m_le_n. generalize dependent o.
  induction m_le_n as [| pn m_le_pn IH]; intros.
  - assumption.
  - apply le_loose in H. apply IH in H. assumption.
Qed.

Theorem O_le_n : ∀ n : nat, 0 ≤ n.
Proof.
  intros n.
  induction n as [| n' IH].
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem n_le_m__Sn_le_Sm : ∀ n m : nat,
  n ≤ m → S n ≤ S m.
Proof.
  intros n m n_le_m.
  induction n_le_m as [| pm n_le_pm IH].
  - apply le_n.
  - apply le_S. assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : ∀ n m : nat,
  S n ≤ S m → n ≤ m.
Proof.
  intros n m sn_le_sm.
  inversion sn_le_sm as [ n_is_m | m' sn_le_m m'_is_m ].
  - apply le_n.
  - apply le_loose. assumption.
Qed.

Theorem le_plus_l : ∀ a b : nat,
  a ≤ a + b.
Proof.
  induction b as [| b' IH].
  - rewrite <- plus_n_O.
    apply le_n.
  - rewrite <- plus_n_Sm.
    apply le_S. assumption.
Qed.

Theorem plus_le : forall n m o : nat,
  n + m ≤ o -> n ≤ o.
Proof.
  induction m as [| m' IH].
  - rewrite <- plus_n_O. intros. assumption.
  - rewrite <- plus_n_Sm. intros o s_nm_le_o.
    apply le_loose in s_nm_le_o.
    apply IH. assumption.
Qed.

Lemma plus_lt_l : forall n m o : nat,
  n + m < o -> n < o.
Proof.
  unfold lt. simpl.
  (* S n + m ≤ o -> S n ≤ o *)
  intros. apply plus_le with m. assumption.
Qed.

Lemma plus_lt_r : forall n m o : nat,
  n + m < o -> m < o.
Proof.
  intros n m o.
  rewrite add_comm. apply plus_lt_l.
Qed.

Theorem plus_lt : ∀n1 n2 m,
  n1 + n2 < m → n1 < m ∧ n2 < m.
Proof.
  intros. split.
  - apply plus_lt_l with n2. assumption.
  - apply plus_lt_r with n1. assumption.
Qed.

Theorem lt_S : forall n m : nat,
  n < m → n < S m.
Proof.
  intros. apply le_S. assumption.
Qed.

Theorem leb_complete : ∀ n m : nat,
  n <=? m = true → n ≤ m.
Proof.
  intros until m. generalize dependent n.
  induction m as [| m' IH]; intros n n_le_m_true.
  - destruct n as [| n'].
    + apply le_n.
    + simpl in n_le_m_true. discriminate n_le_m_true.
  - destruct n as [| n'].
    + apply O_le_n.
    + simpl in n_le_m_true.
      apply n_le_m__Sn_le_Sm.
      apply IH. assumption.
Qed.

Theorem leb_refl : ∀ n : nat,
  n <=? n = true.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. apply IH.
Qed.

Theorem leb_loose : ∀ n m : nat,
  n <=? m = true → n <=? S m = true.
Proof.
  induction n as [| n' IH]; intros m n_leb_m_true.
  - reflexivity.
  - destruct m as [| m']; simpl in n_leb_m_true.
    + discriminate n_leb_m_true.
    + apply IH. assumption.
Qed.

Lemma leb_correct : ∀ n m : nat,
  n ≤ m → n <=? m = true.
Proof.
  intros n m n_le_m.
  induction n_le_m as [| pm n_le_pm IH].
  - apply leb_refl.
  - apply leb_loose. assumption.
Qed.

Theorem leb_true_trans : ∀ n m o : nat,
  n <=? m = true → m <=? o = true → n <=? o = true.
Proof.
  intros n m o H I.
  apply leb_complete in H. apply leb_complete in I.
  apply leb_correct. apply le_trans with m; assumption.
Qed.

Theorem leb_iff : ∀ n m : nat,
  n <=? m = true ↔ n ≤ m.
Proof.
  split; solve [apply leb_correct | apply leb_complete].
Qed.

Inductive R : nat → nat → nat → Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o) : R (S m) n (S o)
  | c3 m n o (H : R m n o) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o) : R n m o
.

Example one_plus_one_is_two : R 1 1 2.
Proof.
  apply c2. apply c3. apply c1.
Qed.

Definition fR : nat → nat → nat := plus.

Theorem R_0_n : ∀ n : nat, R 0 n n.
Proof.
  induction n.
  - apply c1.
  - apply c3. assumption.
Qed.

Module PlusR.

Theorem plus_R : ∀ m n o : nat,
  m + n = o → R m n o.
Proof.
  induction m as [| m' IH]; simpl; intros n o m_plus_n_eq_o.
  - rewrite m_plus_n_eq_o. apply R_0_n.
  - destruct o as [| o'].
    + discriminate m_plus_n_eq_o.
    + injection m_plus_n_eq_o. intros m'_plus_n_eq_o'.
      apply IH in m'_plus_n_eq_o'.
      apply c2. assumption.
Qed.

Theorem R_plus : ∀ m n o : nat,
  R m n o → m + n = o.
Proof.
  intros m n o rmno.
  induction rmno as [
    | m' n o' rm'no' IH
    | m n' o' rmn'o' IH
    | m' n' o'' rm'n'o'' IH
    | m n o rnmo IH ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - rewrite <- plus_n_Sm. rewrite IH. reflexivity.
  - rewrite <- plus_n_Sm in IH. simpl in IH. inversion IH. reflexivity.
  - rewrite add_comm. assumption.
Qed.

Lemma R_equiv_fR : forall m n o : nat, R m n o ↔ fR m n = o.
Proof.
  unfold fR. intros. split.
  - apply R_plus.
  - apply plus_R.
Qed.

End PlusR.

Require Import List.
Import ListNotations.

Inductive subseq : list nat → list nat → Prop :=
  | sub_nil : ∀ xs, subseq [] xs
  | sub_cons_r : ∀ (y : nat) (xs ys : list nat),
        subseq xs ys -> subseq xs (y :: ys)
  | sub_cons : ∀ (x : nat) (xs ys : list nat),
        subseq xs ys -> subseq (x :: xs) (x :: ys)
.

Theorem subseq_refl : ∀(l : list nat), subseq l l.
Proof.
  induction l as [| h t IH].
  - apply sub_nil.
  - apply sub_cons. apply IH.
Qed.

Theorem subseq_app : ∀ l1 l2 l3 : list nat,
  subseq l1 l2 → subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 sub_l1l2.
  induction sub_l1l2 as
    [ l2
    | h2 l1 t2 sub_l1t2 IH
    | h t1 t2 sub_t1t2 IH ].
  - apply sub_nil.
  - simpl. apply sub_cons_r. apply IH.
  - simpl. apply sub_cons. apply IH.
Qed.

Theorem sub_nil_nil : ∀ xs : list nat,
  subseq xs [] → xs = [].
Proof.
  intros xs H.
  inversion H.
  reflexivity.
Qed.

Theorem subseq_trans : ∀ l1 l2 l3 : list nat,
  subseq l1 l2 → subseq l2 l3 → subseq l1 l3.
Proof.
  intros l1 l2 l3 sub_l1l2 sub_l2l3.
  generalize dependent l1.
  induction sub_l2l3 as [l3 | h3 l2 t3 sub_l2t3 IH | h t2 t3 sub_t2t3 IH ]
    ; intros.
  - apply sub_nil_nil in sub_l1l2. rewrite sub_l1l2. apply sub_nil.
  - apply IH in sub_l1l2. apply sub_cons_r. assumption.
  - inversion sub_l1l2.
    + apply sub_nil.
    + apply IH in H1. apply sub_cons_r. assumption.
    + apply IH in H1. apply sub_cons. assumption.
Qed.

Module NeverLess2R.

Inductive R : nat → list nat → Prop :=
  | c1 : R 0 []
  | c2 : ∀n l, R n l → R (S n) (n :: l)
  | c3 : ∀n l, R (S n) l → R n l.

Example example1 : R 2 [1; 0].
Proof.
  repeat apply c2. apply c1.
Qed.

Example example2 : R 1 [1;2;1;0].
Proof.
  apply c3. apply c2.
  apply c3. apply c3. repeat apply c2.
  apply c1.
Qed.

End NeverLess2R.

