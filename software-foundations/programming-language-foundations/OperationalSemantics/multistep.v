Require Import OperationalSemantics.tm.
Require Import OperationalSemantics.relations.
Require Import Relations.

Inductive multi {X : Type} (R : relation X) : relation X :=
| multi_refl : ∀ (x : X), multi R x x
| multi_step : ∀ (x y z : X), R x y → multi R y z → multi R x z.

Notation "t '-->*' t'" := (multi step t t') (at level 40).

Theorem multi_R : ∀ {X : Type} (R : relation X) (x y : X),
  R x y → multi R x y.
Proof.
  intros X R x y Rxy.
  apply multi_step with y.
  - assumption.
  - constructor.
Qed.

Theorem multi_trans : ∀ {X : Type} (R : relation X) (x y z : X),
  multi R x y → multi R y z → multi R x z.
Proof.
  intros X R x y z Rxy Ryz.
  induction Rxy.
  - assumption.
  - eapply multi_step; eauto.
Qed.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  t -->* t' ∧ step_normal_form t'.

Lemma normal_form_no_step : ∀ t t', normal_form step t → ¬ t --> t'.
Proof.
  intros t t' NF Rtt'.
  unfold normal_form in NF.
  now assert (∃ t'', t --> t'') as NNF by
    now exists t'.
Qed.

Theorem normal_forms_unique: deterministic normal_form_of.
Proof.
  intros X y1 y2 [P11 P12] [P21 P22].
  generalize dependent y2.
  unfold step_normal_form in *.
  induction P11; intros y2 P21 P22.
  - inversion P21; subst.
    + reflexivity.
    + now assert (¬ x --> y) as NH by
        now apply normal_form_no_step.
  - inversion P21; subst.
    + now assert (¬ y2 --> y) as NH by
        now apply normal_form_no_step.
    + apply IHP11; try trivial.
      assert (y = y0) as Ey by now apply step_deterministic with x.
      now rewrite Ey.
Qed.

Theorem multistep_congr_1 : ∀ t1 t2 t1',
  t1 -->* t1' → P t1 t2 -->* P t1' t2.
Proof.
  intros t1 t2 t1' H.
  induction H.
  - constructor.
  - apply multi_step with (P y t2).
    + apply ST_Plus1. assumption.
    + assumption.
Qed.

Theorem multistep_congr_2 : ∀ t1 t2 t2',
  value t1 → t2 -->* t2' → P t1 t2 -->* P t1 t2'.
Proof.
  intros t1 t2 t2' Vt1 H.
  induction H.
  - constructor.
  - apply multi_step with (P t1 y).
    + now apply ST_Plus2.
    + assumption.
Qed.

Definition normalizing {X : Type} (R : relation X) :=
  ∀ t, ∃ t', multi R t t' ∧ normal_form R t'.

Theorem step_normalizing : normalizing step.
Proof.
  intros t. induction t.
  - exists (C n). split.
    + constructor.
    + intros [t' S]. inversion S.
  - destruct IHt1 as [t1' [S1 NF1]].
    destruct IHt2 as [t2' [S2 NF2]].
    apply nf_same_as_value in NF1. inversion NF1.
    apply nf_same_as_value in NF2. inversion NF2.
    subst.
    exists (C (n + n0)).
    split.
    apply multi_trans with (P (C n) t2).
    now apply multistep_congr_1.
    apply multi_trans with (P (C n) (C n0)).
    now apply multistep_congr_2.
    apply multi_step with (C (n + n0)).
    constructor. constructor.
    apply nf_same_as_value. constructor.
Qed.
