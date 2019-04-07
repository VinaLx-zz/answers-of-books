Require Import Utf8.
Require Import Nat.

Inductive aexp : Type :=
| ANum (n : nat)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: ∀a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  - (* APlus *)
    destruct a1; try
      (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity.
Qed.


Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue  => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end
.

Theorem optimize_0plus_b_sound :
  ∀ b, beval (optimize_0plus_b b) = beval b.
Proof.
  induction b;
  simpl; repeat rewrite optimize_0plus_sound; try reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Reserved Notation "e '\\' n" (at level 90, left associativity).
Inductive aevalR : aexp → nat → Prop :=
| E_ANum (n : nat) :
    ANum n \\ n
| E_APlus {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 → e2 \\ n2 → APlus e1 e2 \\ n1 + n2
| E_AMinus {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 → e2 \\ n2 → AMinus e1 e2 \\ n1 - n2
| E_AMult {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 → e2 \\ n2 → AMult e1 e2 \\ n1 * n2

where "e '\\' n" := (aevalR e n) : type_scope.

Reserved Notation "e '\\\' b" (at level 90, left associativity).

Inductive bevalR : bexp → bool → Prop :=
| E_BTrue  : bevalR BTrue true
| E_BFalse : bevalR BFalse false
| E_BEq {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 → e2 \\ n2 → BEq e1 e2 \\\ n1 =? n2
| E_BLe {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 → e2 \\ n2 → BLe e1 e2 \\\ n1 <=? n2
| E_BNot {a1 : bexp} {b : bool} :
    a1 \\\ b → BNot a1 \\\ negb b
| E_BAnd {a1 a2 : bexp} {b1 b2 : bool}:
    a1 \\\ b1 → a2 \\\ b2 → BAnd a1 a2 \\\ andb b1 b2

where "e '\\\' b" := (bevalR e b) : type_scope.


Theorem aeval_iff_aevalR : ∀a n,
  (a \\ n) ↔ aeval a = n.
Proof.
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Lemma beval_bevalR : ∀ b bv, beval b = bv → bevalR b bv.
Proof.
  induction b; simpl; intros; try rewrite <- H;
  try (remember (aeval a1) as n1 eqn: E1; remember (aeval a2) as n2 eqn: E2);
  try constructor;
  try (apply aeval_iff_aevalR; symmetry; assumption).
  - apply IHb. reflexivity.
  - apply IHb1. reflexivity.
  - apply IHb2. reflexivity.
Qed.

Lemma bevalR_beval : ∀ b bv, bevalR b bv → beval b = bv.
Proof.
  intros. induction H; simpl;
  try (apply aeval_iff_aevalR in H; rewrite H);
  try (apply aeval_iff_aevalR in H0; rewrite H0); try reflexivity.
  - rewrite IHbevalR. reflexivity. 
  - rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.
Qed.

Lemma beval_iff_bevalR : ∀ b bv, bevalR b bv ↔ beval b = bv.
Proof.
  intros. split; solve [apply beval_bevalR | apply bevalR_beval].
Qed.
