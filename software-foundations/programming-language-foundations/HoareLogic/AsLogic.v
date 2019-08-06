Require Import HoareLogic.ProofRules.
Require Import LF.Imp.
Require Import Utf8.
Require Import Bool.

Inductive hoare_proof : Assertion → com → Assertion → Type :=
| H_Skip : ∀ P, hoare_proof P SKIP P
| H_Asgn : ∀ Q V a,
  hoare_proof (assn_sub V a Q) (V ::= a) Q
| H_Seq : ∀ P c Q d R,
  hoare_proof P c Q → hoare_proof Q d R → hoare_proof P (c ;; d) R
| H_If : ∀ P Q b t f,
  hoare_proof (fun st => P st ∧   bassn b st) t Q →
  hoare_proof (fun st => P st ∧ ¬ bassn b st) f Q →
  hoare_proof P (TEST b THEN t ELSE f FI) Q
| H_While : ∀ P b c,
  hoare_proof (fun st => P st ∧ bassn b st) c P →
  hoare_proof P (WHILE b DO c END) (fun st => P st ∧ ¬ bassn b st)
| H_Consequence : ∀ P Q P' Q' c,
  hoare_proof P' c Q' → P ->> P' → Q' ->> Q →
  hoare_proof P c Q
.

Lemma H_Consequence_pre : ∀ P Q P' c,
  hoare_proof P' c Q → P ->> P' → hoare_proof P c Q.
Proof.
  intros.
  eapply H_Consequence.
  - eassumption.
  - eassumption.
  - apply implies_refl.
Qed.

Lemma H_Consequence_post : ∀ P Q Q' c,
  hoare_proof P c Q' → Q' ->> Q → hoare_proof P c Q.
Proof.
  intros.
  eapply H_Consequence.
  - eassumption.
  - apply implies_refl.
  - eassumption.
Qed.

Theorem hoare_proof_sound : ∀ P c Q,
  hoare_proof P c Q → {{ P }} c {{ Q }}.
Proof.
  intros P c Q H.
  induction H.
  - apply hoare_skip.
  - apply hoare_assign.
  - apply hoare_seq with Q; assumption.
  - apply hoare_if; assumption.
  - apply hoare_while. assumption.
  - apply hoare_consequence_pre with P'.
    apply hoare_consequence_post with Q'.
    all: assumption.
Qed.

Definition wp (c : com) (Q : Assertion) : Assertion :=
  fun st => ∀ st', st =[ c ]=> st' → Q st'.

Lemma wp_is_precondition : ∀ c Q,
  {{ wp c Q }} c {{ Q }}.
Proof.
  intros c Q st st' E w.
  unfold wp in w.
  apply w.
  assumption.
Qed.

Lemma wp_is_weakest : ∀ c Q P',
  {{ P' }} c {{ Q }} → P' ->> wp c Q.
Proof.
  unfold hoare_triple. unfold wp.
  intros c Q P' H st P'st st' E.
  apply H with st; trivial.
Qed.

Lemma bassn_eval_false : ∀ b st, ¬ bassn b st → beval st b = false.
Proof.
  unfold bassn.
  intros b st nbassn.
  now apply not_true_is_false in nbassn.
Qed.

Theorem hoare_proof_complete : ∀ P c Q,
  {{ P }} c {{ Q }} → hoare_proof P c Q.
Proof.
  intros P c. generalize dependent P.
  induction c; intros P Q C.
  - eapply H_Consequence.
    + apply H_Skip.
    + apply implies_refl.
    + intros st. apply C. constructor.
  - eapply H_Consequence.
    + apply H_Asgn.
    + intros st. apply C. now constructor.
    + apply implies_refl.
  - apply H_Seq with (wp c2 Q).
    + apply IHc1.
      intros st st' C1 Pst st'' H.
      apply C with st.
      ++ econstructor; eauto.
      ++ trivial.
    + apply IHc2. apply wp_is_precondition.
  - apply H_If.
    + apply IHc1. intros st st' C1 [Pst B].
      apply C with st; auto.
      apply E_IfTrue; trivial.
    + apply IHc2. intros st st' C2 [Pst nB].
      apply C with st; auto.
      apply E_IfFalse.
      ++ now apply bassn_eval_false.
      ++ trivial.
  - eapply H_Consequence.
    apply H_While.
    2: eapply wp_is_weakest; eassumption.
    + apply IHc. admit.
    + intros st [WP NB]. eapply C.
      ++ apply E_WhileFalse. now apply bassn_eval_false.
      ++ 
Admitted.

