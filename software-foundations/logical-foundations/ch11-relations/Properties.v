Require Import Utf8.
Require Import Relations.
Require Import PeanoNat.

Definition reflexive {X: Type} (R: relation X) :=
  ∀ a : X, R a a.

Definition partial_function {X: Type} (R: relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Inductive total_relation (m n : nat) : Prop :=
  | total_mn : total_relation m n.

Theorem total_relation_not_function : ¬ (partial_function total_relation).
Proof.
  unfold partial_function. intro.
  assert (0 = 1) as nonsense.
  - apply H with (x := 0); apply total_mn.
  - discriminate nonsense.
Qed.

Inductive empty_relation (m n : nat) : Prop :=.

Theorem empty_relation_function : partial_function empty_relation.
Proof.
  unfold partial_function. intros.
  inversion H.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  ∀ a b c : X, R a b → R b c → R a c.

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo. Qed.

(* Prove this by induction on evidence that m is less than o. *)
Theorem lt_trans' : transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S. assumption.
  - apply le_S. assumption.
Qed.

(* Prove the same thing again by induction on o. *)
Theorem lt_trans'' : transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros m n o. generalize dependent n. generalize dependent m.
  induction o as [| o' IH].
  - intros. inversion H0.
  - intros. remember (S o') as so'. destruct H0.
    + apply le_S. assumption.
    + injection Heqso'. intro. rewrite <- H1 in IH.
      apply le_S. apply IH with (n := n); assumption.
Qed.

Theorem le_Sn_le : ∀n m, S n ≤ m → n ≤ m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_Sn_n : ∀ n, ¬ (S n ≤ n).
Proof.
  intros. intro.
  induction n.
  - inversion H.
  - apply IHn. apply le_S_n. assumption.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  ∀ a b : X, (R a b) → (R b a).

Theorem le_not_symmetric : ¬ (symmetric le).
Proof.
  unfold symmetric. intro.
  assert (1 ≤ 0) as nonsense.
  - apply H. repeat constructor.
  - inversion nonsense.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  ∀ a b : X, (R a b) → (R b a) → a = b.

Theorem le_antisymmetric : antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a b ab ba.
  inversion ab.
  - reflexivity.
  - assert (S b ≤ b) as nonsense.
    + apply le_trans with (b := S a).
      apply le_n_S. assumption.
      rewrite <- H0. apply le_n_S. assumption.
    + apply le_Sn_n in nonsense. contradiction .
Qed.

Theorem le_step : ∀ n m p,
  n < m → m ≤ S p → n ≤ p.
Proof.
  unfold lt. intros.
  cut (S n ≤ S p).
  - apply le_S_n.
  - apply le_trans with (b := m); assumption.
Qed.

Inductive clos_refl_trans_1n {A : Type} (R : relation A) (x : A)
                             : A → Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_trans :
  ∀ (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y →
      clos_refl_trans_1n R y z →
      clos_refl_trans_1n R x z.
Proof.
  intros X R x y z rxy. generalize dependent z.
  induction rxy; intros.
  - assumption.
  - apply IHrxy in H.
    apply rt1n_trans with (y0 := y); assumption.
Qed.

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.

Lemma rsc_R : ∀(X:Type) (R:relation X) (x y : X),
       R x y → clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.

Lemma rtc_rsc :
  ∀ (X : Type) (R : relation X) (x y : X),
    clos_refl_trans R x y → clos_refl_trans_1n R x y.
Proof.
  intros. induction H.
  - apply rsc_R. assumption.
  - apply rt1n_refl.
  - apply rsc_trans with (y := y); assumption.
Qed.

Lemma rsc_rtc : 
  ∀ (X : Type) (R : relation X) (x y : X),
    clos_refl_trans_1n R x y → clos_refl_trans R x y.
Proof.
  intros. induction H.
  - apply rt_refl.
  - apply rt_trans with (y0 := y).
    + apply rt_step. assumption.
    + assumption.
Qed.

Theorem rtc_rsc_coincide : ∀ (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y ↔ clos_refl_trans_1n R x y.
Proof.
  split.
  - apply rtc_rsc.
  - apply rsc_rtc.
Qed.

