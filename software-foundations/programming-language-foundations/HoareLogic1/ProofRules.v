Require Import LF.Imp.
Require Import Utf8.
Require Import PeanoNat. Import Nat.

Definition Assertion := state → Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  ∀ st, P st → Q st.

Bind Scope hoare_spec_scope with Assertion.

Notation "P ->> Q" := (assert_implies P Q) (at level 80) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q ∧ Q ->> P) (at level 80) : hoare_spec_scope.

Close Scope hoare_spec_scope.

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  ∀ st st', st =[ c ]=> st' → P st → Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level) : hoare_spec_scope.

Open Scope hoare_spec_scope.

Theorem hoare_post_true : ∀ (P Q : Assertion) c,
  (∀ st, Q st) → {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple. intros.
  apply H.
Qed.

Theorem hoare_pre_false : ∀ (P Q : Assertion) c,
  (∀ st, ¬ P st) → {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple. intros.
  apply H in H1. contradiction.
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) => P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" :=
  (assn_sub X a P) (at level 10, X at next level).

Theorem hoare_assign : ∀ Q X a,
  {{ Q [ X |-> a ] }} X ::= a {{ Q }}.
Proof.
  unfold hoare_triple. intros.
  unfold assn_sub in H0.
  inversion H. subst.
  assumption.
Qed.

Theorem hoare_assign_forward : ∀ m a P X,
  {{ fun st => P st ∧ st X = m }}
    X ::= a
  {{ fun st => P (X !-> m ; st) ∧ st X = aeval (X !-> m ; st) a }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst.
  destruct H0 as [Pst stXm].
  rewrite t_update_shadow.
  rewrite <- stXm.
  rewrite t_update_same.
  split.
  - assumption.
  - unfold t_update. rewrite <- eqb_string_refl. reflexivity.
Qed.

Theorem hoare_assign_forward_exists : ∀ a P X,
  {{ P }}
    X ::= a
  {{ fun st => ∃ m, P (X !-> m ; st) ∧ st X = aeval (X !-> m; st) a }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst.
  exists (st X).
  rewrite t_update_shadow.
  rewrite t_update_same.
  unfold t_update.
  rewrite <- eqb_string_refl.
  easy.
Qed.

Theorem hoare_consequence_pre : ∀ (P P' Q : Assertion) c,
  {{ P' }} c {{ Q }} → P ->> P' → {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple. intros.
  eapply H.
  - apply H1.
  - apply H0. assumption.
Qed.

Theorem hoare_consequence_post : ∀ (P Q Q' : Assertion) c,
  {{ P }} c {{ Q' }} → Q' ->> Q → {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple. intros.
  apply H0.
  eapply H.
  - apply H1.
  - apply H2.
Qed.

Theorem hoare_consequence : ∀ (P P' Q Q' : Assertion) c,
  {{ P' }} c {{ Q' }} →
  P ->> P' → Q' ->> Q →
  {{ P }} c {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence_pre.
  eapply hoare_consequence_post.
  apply H. apply H1. apply H0.
Qed.

Theorem hoare_skip : ∀ P,
  {{ P }} SKIP {{ P }}.
Proof.
  unfold hoare_triple.
  intros. inversion H. subst. assumption.
Qed.

Theorem hoare_seq : ∀ P Q R a b,
  {{ Q }} b {{ R }} → {{ P }} a {{ Q }} →
  {{ P }} a ;; b {{ R }}.
Proof.
  unfold hoare_triple. intros.
  inversion H1. subst.
  eapply H. eassumption.
  eapply H0; eassumption.
Qed.

Example hoare_assign_example :
  {{ fun st => True }}
    X ::= 1 ;; Y ::= 2
  {{ fun st => st X = 1 ∧ st Y = 2 }}.
Proof.
  intros.
  eapply hoare_consequence_pre.
  eapply hoare_seq.
  eapply hoare_assign.
  eapply hoare_assign.
  (* {{ True }} ->> {{ 1 = 1 ∧ 2 = 2 }} *)
  intros st T.
  unfold assn_sub. unfold t_update. simpl.
  easy.
Qed.

Theorem implies_refl : ∀ A, A ->> A.
Proof.
  unfold assert_implies.
  intros.
  assumption.
Qed.

Definition swap_program : com :=
  Z ::= X ;; X ::= Y ;; Y ::= Z.

Theorem swap_exercise :
  {{ fun st => st X ≤ st Y }}
    swap_program
  {{ fun st => st Y ≤ st X }}.
Proof.
  unfold swap_program.
  eapply hoare_seq.
  all: cycle 1.
  eapply hoare_consequence_pre.
  eapply hoare_assign.
  all: cycle 1.
  eapply hoare_seq.
  eapply hoare_consequence_post.
  eapply hoare_assign.
  2: eapply hoare_assign.
  apply implies_refl.
  unfold assert_implies.
  intros.
  unfold assn_sub. unfold t_update.
  assumption.
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : ∀ b st,
  beval st b = true → (bassn b) st.
Proof.
  intros. unfold bassn. simpl. assumption.
Qed.

Lemma bexp_eval_false : ∀ b st,
  beval st b = false → ¬ (bassn b) st.
Proof.
  intros. unfold bassn. simpl. 
  rewrite H. easy.
Qed.

Hint Resolve bexp_eval_true bexp_eval_false.

Theorem hoare_if : ∀ P Q b t f,
  {{ fun st => P st ∧   bassn b st }} t {{ Q }} →
  {{ fun st => P st ∧ ¬ bassn b st }} f {{ Q }} →
  {{ P }} TEST b THEN t ELSE f FI {{ Q }}.
Proof.
  unfold hoare_triple.
  intros P Q b t f Ht Hf st st' H Pst.
  inversion H; subst.
  - eapply Ht; eauto.
  - eapply Hf; eauto.
Qed.

Require Omega.

Theorem if_minus_plus :
  {{ fun st => True }}
    TEST X ≤ Y
      THEN Z ::= Y - X
      ELSE Y ::= X + Z
    FI
  {{ fun st => st Y = st X + st Z }}.
Proof.
  apply hoare_if; unfold bassn; simpl.
  - eapply hoare_consequence_pre.
    apply hoare_assign.
    unfold assn_sub.
    intros st [_ b]. unfold t_update.
    simpl. apply leb_le in b. Omega.omega.
  - eapply hoare_consequence_pre.
    apply hoare_assign.
    unfold assn_sub.
    intros st [_ b]. simpl.
    unfold t_update. reflexivity.
Qed.

Theorem hoare_while : ∀ P b c,
  {{ fun st => P st ∧ bassn b st }} c {{ P }} →
  {{ P }} WHILE b DO c END {{ fun st => P st ∧ ¬ (bassn b st) }}.
Proof.
  unfold hoare_triple. intros P b c HH st st' HE Pst.
  remember (WHILE b DO c END)%imp as C.
  induction HE; inversion HeqC; subst; clear HeqC.
  - auto.
  - apply IHHE2. trivial. eapply HH; eauto.
Qed.
