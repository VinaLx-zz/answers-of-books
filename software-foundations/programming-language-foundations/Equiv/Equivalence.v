Require Export LF.Imp.
Require Export Utf8.

Definition aequiv (a1 a2 : aexp) : Prop :=
  ∀ st, aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  ∀ st, beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  ∀ st st', st =[ c1 ]=> st' ↔ st =[ c2 ]=> st'.

Theorem skip_left : ∀ c, cequiv (SKIP ;; c) c.
Proof.
  intros c st st'. split; intros.
  - inversion H; subst. inversion H2. subst. assumption.
  - apply E_Seq with st. constructor. assumption.
Qed.

Theorem skip_right : ∀ c, cequiv (c ;; SKIP) c.
Proof.
  intros c. split; intros.
  - inversion H. subst. inversion H5. subst. assumption.
  - apply E_Seq with st'. assumption. constructor.
Qed.

Theorem TEST_true : ∀ b c1 c2,
  bequiv b BTrue → cequiv (TEST b THEN c1 ELSE c2 FI) c1.
Proof.
  intros b c1 c2 Hbeq st st'.
  unfold bequiv in Hbeq. simpl in Hbeq.
  split; intros.
  - inversion H; subst.
    + assumption.
    + rewrite Hbeq in H5. discriminate H5.
  - apply E_IfTrue. auto. assumption.
Qed.

Theorem TEST_false : ∀ b c1 c2,
  bequiv b BFalse → cequiv (TEST b THEN c1 ELSE c2 FI) c2.
Proof.
  intros b c1 c2 Hbeq st st'.
  unfold bequiv in Hbeq. simpl in Hbeq.
  split; intros.
  - inversion H; subst.
    + rewrite Hbeq in H5. discriminate H5.
    + assumption.
  - apply E_IfFalse. auto. assumption.
Qed.

Lemma test_false_true_swap : ∀ st st' b1 b2 e1 e2,
  beval st b1 = true → beval st b2 = false →
  st =[ TEST b1 THEN e1 ELSE e2 FI ]=> st' ↔
  st =[ TEST b2 THEN e2 ELSE e1 FI ]=> st'.
Proof.
  intros st st' b1 b2 e1 e2 Eb1t Eb2f. split; intros; inversion H; subst.
  - apply E_IfFalse; assumption.
  - rewrite Eb1t in H5. inversion H5.
  - rewrite Eb2f in H5. inversion H5.
  - apply E_IfTrue; assumption.
Qed.

Lemma beval_not : ∀ st be b,
  beval st be = b → beval st (BNot be) = negb b.
Proof.
  intros. simpl. rewrite H. reflexivity.
Qed.

Theorem swap_if_branches : ∀ b e1 e2,
  cequiv
    (TEST b THEN e1 ELSE e2 FI)
    (TEST BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'.
  destruct (beval st b) eqn: E.
  - apply test_false_true_swap. assumption.
    apply beval_not in E. simpl in E. assumption.
  - apply and_comm. apply test_false_true_swap.
    apply beval_not in E. simpl in E. assumption.
    assumption.
Qed.

Lemma WHILE_true_nonterm : ∀ b c st st',
  bequiv b BTrue → ¬ ( st =[ WHILE b DO c END ]=> st' ).
Proof.
  intros b c st st' Hb. intros H.
  remember (WHILE b DO c END)%imp as cw eqn: Heqcw.
  induction H; inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in Hb. rewrite Hb in H. inversion H.
  - apply IHceval2. reflexivity.
Qed.
  
Theorem WHILE_true : ∀ b c,
  bequiv b true →
  cequiv (WHILE b DO c END) (WHILE true DO SKIP END).
Proof.
  intros b c be. split; intros H.
  - apply WHILE_true_nonterm in H. inversion H. assumption.
  - apply WHILE_true_nonterm in H. inversion H.
    unfold bequiv. reflexivity.
Qed.

Theorem WHILE_false : ∀ b c,
  bequiv b false →
  cequiv (WHILE b DO c END) SKIP.
Proof.
  intros b c be st st'. split; intros H.
  - inversion H; subst. constructor.
    rewrite be in H2. simpl in H2. discriminate H2.
  - inversion H. subst.
    apply E_WhileFalse. rewrite be. reflexivity.
Qed.

Theorem seq_assoc : ∀ c1 c2 c3,
  cequiv ((c1 ;; c2) ;; c3) (c1 ;; (c2 ;; c3)).
Proof.
  intros c1 c2 c3 st st'. split; intro.
  - inversion H. subst. inversion H2. subst.
    apply E_Seq with st'1. assumption.
    apply E_Seq with st'0; assumption.
  - inversion H. subst. inversion H5. subst.
    apply E_Seq with st'1. apply E_Seq with st'0.
    assumption. assumption. assumption.
Qed.

Theorem identity_assignment : ∀ x,
  cequiv (x ::= x) SKIP.
Proof.
  intros x st st'. split; intros.
  - inversion H. subst.
    rewrite t_update_same. constructor.
  - inversion H. subst.
    assert (st' =[ x ::= x ]=> (x !-> st' x ; st')) as Hx.
    + apply E_Ass. reflexivity.
    + rewrite t_update_same in Hx. assumption.
Qed.

Theorem assign_aequiv : ∀ x e,
  aequiv (AId x) e → cequiv SKIP (x ::= e).
Proof.
  intros x e Exe st st'.
  unfold aequiv in Exe. simpl in Exe. (* ∀ st, st x = aeval st e *)
  split; intros.
  - inversion H. subst. 
    assert (st' =[ x ::= e ]=> (x !-> st' x ; st')) as Hx.
    + apply E_Ass. auto.
    + rewrite t_update_same in Hx. assumption.
  - inversion H. subst.
    symmetry in Exe. rewrite Exe. rewrite t_update_same.
    constructor.
Qed.
