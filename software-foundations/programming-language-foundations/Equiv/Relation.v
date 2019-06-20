Require Export Equiv.Equivalence.

Hint Unfold aequiv bequiv.

Lemma refl_aequiv : ∀ a, aequiv a a.
Proof. auto. Qed.

Lemma sym_aequiv : ∀ a b, aequiv a b → aequiv b a.
Proof. auto. Qed.

Lemma trans_aequiv : ∀ a b c, aequiv a b → aequiv b c → aequiv a c.
Proof. congruence. Qed.

Lemma refl_bequiv : ∀ a, bequiv a a.
Proof. auto. Qed.

Lemma sym_bequiv : ∀ a b, bequiv a b → bequiv b a.
Proof. auto. Qed.

Lemma trans_bequiv : ∀ a b c, bequiv a b → bequiv b c → bequiv a c.
Proof. congruence. Qed.

Lemma refl_cequiv : ∀ a, cequiv a a.
Proof. intros a st st'. split; auto. Qed.

Lemma sym_cequiv : ∀ a b, cequiv a b → cequiv b a.
Proof. intros a b H st st'. split; apply H. Qed.

Lemma trans_cequiv : ∀ a b c, cequiv a b → cequiv b c → cequiv a c.
Proof.
  unfold cequiv. intros a b c Hab Hbc st st'.
  split; intros H; [> apply Hbc; apply Hab | apply Hab; apply Hbc];
  assumption.
Qed.

Theorem cong_assignment : ∀ x a1 a2,
  aequiv a1 a2 → cequiv (x ::= a1) (x ::= a2).
Proof.
  intros x a1 a2 Ha; split; intros Hc;
  inversion Hc; subst; apply E_Ass; auto.
Qed.

Theorem cong_while_one : ∀ b1 b2 c1 c2 st st',
  bequiv b1 b2 → cequiv c1 c2 →
  st =[ WHILE b1 DO c1 END ]=> st' →
  st =[ WHILE b2 DO c2 END ]=> st'.
Proof.
  intros b1 b2 c1 c2 st st' Eb1b2 Ec1c2 H.
  remember (WHILE b1 DO c1 END)%imp eqn: E.
  induction H; inversion E; subst; clear E.
  - apply E_WhileFalse. congruence.
  - apply E_WhileTrue with st'.
    + congruence.
    + apply Ec1c2. assumption.
    + apply IHceval2. reflexivity.
Qed.

Hint Resolve sym_bequiv sym_cequiv.

Theorem cong_while : ∀ b1 b2 c1 c2,
  bequiv b1 b2 → cequiv c1 c2 →
  cequiv (WHILE b1 DO c1 END) (WHILE b2 DO c2 END).
Proof.
  intros b1 b2 c1 c2 Eqb1b2 Eqc1c2 st st'. split;
  apply cong_while_one; auto.
Qed.

Theorem cong_seq_one : ∀ a1 a2 b1 b2 st st',
  cequiv a1 a2 → cequiv b1 b2 →
  st =[ a1 ;; b1 ]=> st' → st =[ a2 ;; b2 ]=> st'.
Proof.
  intros a1 a2 b1 b2 st st' Ea Eb H.
  inversion H. subst.
  apply E_Seq with st'0; [> apply Ea | apply Eb];
  assumption.
Qed.

Theorem cong_seq : ∀ a1 a2 b1 b2,
  cequiv a1 a2 → cequiv b1 b2 → cequiv (a1 ;; b1) (a2 ;; b2).
Proof.
  intros a1 a2 b1 b2 Ea Eb st st'. split;
  apply cong_seq_one; auto.
Qed.

Theorem cong_if_one : ∀ b1 b2 t1 t2 f1 f2 st st',
  bequiv b1 b2 → cequiv t1 t2 → cequiv f1 f2 →
  st =[ TEST b1 THEN t1 ELSE f1 FI ]=> st' →
  st =[ TEST b2 THEN t2 ELSE f2 FI ]=> st'.
Proof.
  intros until st'. intros Eb Et Ef H.
  inversion H; subst.
  - apply E_IfTrue.
    + congruence.
    + apply Et. assumption.
  - apply E_IfFalse.
    + congruence.
    + apply Ef. assumption.
Qed.

Theorem cong_if : ∀ b1 b2 t1 t2 f1 f2,
  bequiv b1 b2 → cequiv t1 t2 → cequiv f1 f2 →
  cequiv
    (TEST b1 THEN t1 ELSE f1 FI)
    (TEST b2 THEN t2 ELSE f2 FI).
Proof.
  intros. intros st st'.
  split; apply cong_if_one; auto.
Qed.
