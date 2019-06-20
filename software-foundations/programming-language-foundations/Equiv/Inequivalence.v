Require Import Equiv.Relation.

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x' => if eqb_string x x' then u else AId x'
  | APlus lhs rhs =>
      APlus (subst_aexp x u lhs) (subst_aexp x u rhs)
  | AMinus lhs rhs =>
      AMinus (subst_aexp x u lhs) (subst_aexp x u rhs)
  | AMult lhs rhs =>
      AMult (subst_aexp x u lhs) (subst_aexp x u rhs)
  end
.

Definition subst_equiv_property := ∀ x y xv yv,
  cequiv
    (x ::= xv ;; y ::= yv)
    (x ::= xv ;; y ::= subst_aexp x xv yv).

Theorem subst_inequiv : ¬ subst_equiv_property.
Proof.
  unfold subst_equiv_property. intro contra.
  set (xexp := (X + 1)%imp).
  set (yexp := X%imp).
  set (c := contra X Y xexp yexp empty_st (Y !-> 1 ; X !-> 1)).
  destruct c as [H _].
  simpl in H.
  assert (empty_st =[ X ::= xexp ;; Y ::= yexp ]=> (Y !-> 1; X !-> 1)) as Sure.
  - apply E_Seq with (X !-> 1).
    apply E_Ass. reflexivity.
    apply E_Ass. reflexivity.
  - apply H in Sure.
    inversion Sure. subst.
    inversion H2. subst.
    simpl in H5. inversion H5. subst. simpl in H6.
    remember (Y !-> 2; X !-> 1) as lst.
    remember (Y !-> 1; X !-> 1) as rst.
    assert (lst Y = rst Y) as impossible by congruence.
    rewrite Heqlst in impossible. rewrite Heqrst in impossible.
    unfold t_update in impossible. inversion impossible.
Qed.

Inductive not_used (x : string) : aexp → Prop :=
| NUNum : ∀ n, not_used x (ANum n)
| NUId : ∀ y, x ≠ y → not_used x (AId y)
| NUPlus : ∀ lhs rhs,
    not_used x lhs → not_used x rhs → not_used x (APlus lhs rhs)
| NUMinus : ∀ lhs rhs,
    not_used x lhs → not_used x rhs → not_used x (AMinus lhs rhs)
| NUMult : ∀ lhs rhs,
    not_used x lhs → not_used x rhs → not_used x (AMult lhs rhs)
.

Lemma aeval_weakening : ∀ x xv a st,
  not_used x a → aeval (x !-> xv; st) a = aeval st a.
Proof.
  intros x xv a st NU.
  induction NU; simpl;
  try (rewrite IHNU1; rewrite IHNU2);
  try reflexivity.

  - unfold t_update. unfold eqb_string.
    destruct string_dec.
    + contradiction.
    + reflexivity.
Qed.

Lemma not_used_subst_equal : ∀ x xv yv st,
  not_used x xv →
  aeval (x !-> aeval st xv; st) (subst_aexp x xv yv) =
  aeval (x !-> aeval st xv; st) yv.
Proof.
  intros. rename H into NU.
  induction yv; simpl;
  try (rewrite IHyv1; rewrite IHyv2);
  try reflexivity.

  - simpl. unfold eqb_string. destruct (string_dec x x0).
    + simpl. rewrite <- e.
      replace ((x !-> aeval st xv; st) x) with (aeval st xv)
        by (unfold t_update; simpl; rewrite <- eqb_string_refl; reflexivity).
      apply aeval_weakening. assumption.
    + reflexivity.
Qed.

Lemma nonsubst_to_subst :
  ∀ x y xv yv st st', not_used x xv →
  st =[ x ::= xv ;; y ::= yv ]=> st' →
  st =[ x ::= xv ;; y ::= subst_aexp x xv yv ]=> st'.
Proof.
  intros until st'. intros NU H.
  inversion H. subst.
  apply E_Seq with st'0.
  - assumption.
  - inversion H2. subst.
    inversion H5. subst.
    apply E_Ass.
    apply not_used_subst_equal. assumption.
Qed.

Lemma subst_to_nonsubst :
  ∀ x y xv yv st st', not_used x xv →
  st =[ x ::= xv ;; y ::= subst_aexp x xv yv ]=> st' →
  st =[ x ::= xv ;; y ::= yv ]=> st'.
Proof.
  intros until st'. intros NU H.
  inversion H. subst.
  apply E_Seq with st'0.
  - assumption.
  - inversion H2. subst.
    inversion H5. subst.
    apply E_Ass. symmetry.
    apply not_used_subst_equal. assumption.
Qed.

Theorem subst_equiv :
  ∀ x y xv yv, not_used x xv → 
    cequiv
      (x ::= xv ;; y ::= yv)
      (x ::= xv ;; y ::= subst_aexp x xv yv).
Proof.
  intros x y xv yv NU st st'.
  split;
  [> apply nonsubst_to_subst | apply subst_to_nonsubst];
  assumption.
Qed.

Theorem dead_loop_inequiv_skip :
  ¬ cequiv (WHILE true DO SKIP END) SKIP.
Proof.
  intros H.
  destruct (H empty_st empty_st) as [_ contra].
  assert (empty_st =[ SKIP ]=> empty_st) as Sure by constructor.
  apply contra in Sure.
  assert (bequiv BTrue BTrue) as E by apply refl_bequiv.
  apply WHILE_true_nonterm with (st := empty_st) (st' := empty_st) in Sure.
  contradiction. assumption.
Qed.
