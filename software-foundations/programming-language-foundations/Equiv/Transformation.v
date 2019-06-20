Require Import Equiv.Relation.
Require Import Nat.

Definition atrans_sound (atrans : aexp → aexp) : Prop :=
  ∀ a, aequiv a (atrans a).

Definition btrans_sound (btrans : bexp → bexp) : Prop :=
  ∀ b, bequiv b (btrans b).

Definition ctrans_sound (ctrans : com → com) : Prop :=
  ∀ c, cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus lhs rhs =>
      match (fold_constants_aexp lhs, fold_constants_aexp rhs) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (lhs', rhs') => APlus lhs' rhs'
      end
  | AMinus lhs rhs =>
      match (fold_constants_aexp lhs, fold_constants_aexp rhs) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (lhs', rhs') => AMinus lhs' rhs'
      end
  | AMult lhs rhs =>
      match (fold_constants_aexp lhs, fold_constants_aexp rhs) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (lhs', rhs') => AMult lhs' rhs'
      end
  end
.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq lhs rhs =>
      match (fold_constants_aexp lhs, fold_constants_aexp rhs) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then BTrue else BFalse
      | (lhs', rhs') => BEq lhs' rhs'
      end
  | BLe lhs rhs =>
      match (fold_constants_aexp lhs, fold_constants_aexp rhs) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then BTrue else BFalse
      | (lhs', rhs') => BLe lhs' rhs'
      end
  | BNot b =>
      match (fold_constants_bexp b) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b' => BNot b'
      end
  | BAnd lhs rhs =>
      match (fold_constants_bexp lhs, fold_constants_bexp rhs) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (lhs', rhs') => BAnd lhs' rhs'
      end
  end
.

Open Scope imp.
Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP => SKIP
  | x ::= a => x ::= (fold_constants_aexp a)
  | c1 ;; c2 => (fold_constants_com c1) ;; (fold_constants_com c2)
  | TEST b THEN t ELSE f FI =>
      match (fold_constants_bexp b) with
      | BTrue => fold_constants_com t
      | BFalse => fold_constants_com f
      | b' => TEST b' THEN fold_constants_com t ELSE fold_constants_com f FI
      end
  | WHILE b DO c END =>
      match (fold_constants_bexp b) with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end
.
Close Scope imp.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a st.
  induction a; simpl; try reflexivity;
  destruct (fold_constants_aexp a1);
  destruct (fold_constants_aexp a2);
  rewrite IHa1; rewrite IHa2;
  reflexivity .
Qed.

Theorem fold_constants_bexp_sound :
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b st.
  induction b; simpl; try reflexivity.
  (* BEq *)
  - remember (fold_constants_aexp a1) as a1' eqn: E1.
    remember (fold_constants_aexp a2) as a2' eqn: E2.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    2 - 3: (subst; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (n =? n0); reflexivity.
  (* BLe *)
  - remember (fold_constants_aexp a1) as a1' eqn: E1.
    remember (fold_constants_aexp a2) as a2' eqn: E2.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    2 - 3: (subst; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (n <=? n0); reflexivity.
  (* BNot *)
  - rewrite IHb. destruct (fold_constants_bexp b); reflexivity.
  - rewrite IHb1. rewrite IHb2.
    destruct (fold_constants_bexp b1);
    destruct (fold_constants_bexp b2);
    reflexivity.
Qed.

Hint Resolve fold_constants_bexp_sound.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. induction c; simpl.
  - apply refl_cequiv.
  - apply cong_assignment. apply fold_constants_aexp_sound.
  - apply cong_seq; assumption.
  - assert (bequiv b (fold_constants_bexp b)) as EqB
      by apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn: E;
    try (apply cong_if; assumption).
    + apply trans_cequiv with c1. 2: assumption.
      apply TEST_true. rewrite <- E. auto.
    + apply trans_cequiv with c2. 2: assumption.
      apply TEST_false. rewrite <- E. auto.
  - assert (bequiv b (fold_constants_bexp b)) as EqB
      by apply fold_constants_bexp_sound.
    destruct (fold_constants_bexp b) eqn: E;
    try (apply cong_while; assumption).
    + apply WHILE_true. assumption.
    + apply WHILE_false. assumption.
Qed.

