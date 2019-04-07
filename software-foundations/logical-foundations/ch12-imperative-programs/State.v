Require Import Utf8.
Require Import TotalMap.
Require Import String.
Require Import Nat.

Definition state : Type := total_map nat.

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
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

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y)  (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y)  (at level 40, left associativity) : imp_scope.
Notation "x ≤ y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'¬' b" :=  (BNot b)  (at level 75, right associativity) : imp_scope.

Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ¬ (X ≤ 4))%imp : bexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x (* <--- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end
.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end
.

Definition empty_st := (_ !-> 0).

Inductive com : Type :=
| CSkip
| CAss (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com)
.

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval : com → state → state → Prop :=
  | E_Skip : ∀ st,
      st =[ SKIP ]=> st
  | E_Ass : ∀ st a1 n x,
      aeval st a1 = n →
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : ∀ c1 c2 st st' st'',
      st =[ c1 ]=> st' →
      st' =[ c2 ]=> st'' →
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : ∀ st st' b c1 c2,
      beval st b = true →
      st =[ c1 ]=> st' →
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : ∀ st st' b c1 c2,
      beval st b = false →
      st =[ c2 ]=> st' →
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : ∀ b st c,
      beval st b = false →
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : ∀ st st' st'' b c,
      beval st b = true →
      st =[ c ]=> st' →
      st' =[ WHILE b DO c END ]=> st'' →
      st =[ WHILE b DO c END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (st' := (X !-> 0)).
  apply E_Ass. reflexivity.
  apply E_Seq with (st' := (Y !-> 1 ; X !-> 0)).
  apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
Qed.

Definition pup_to_n : com :=
  Y ::= 0 ;; 
  WHILE (¬ X = 0) DO
    Y ::= Y + X ;;
    X ::= X - 1
  END.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n.
  apply E_Seq with (st' := Y !-> 0; X !-> 2).
  apply E_Ass. reflexivity.
  apply E_WhileTrue with (st' := X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
  reflexivity.
  apply E_Seq with (st' := Y !-> 2 ; Y !-> 0 ; X !-> 2).
  apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
  apply E_WhileTrue with
    (st' := X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
  reflexivity.
  apply E_Seq with
    (st' := Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
  apply E_Ass. reflexivity.
  apply E_Ass. reflexivity.
  apply E_WhileFalse.
  reflexivity.
Qed.

Definition XtimesYinZ : com := Z ::= X * Y.

Lemma XtimesYinZ_spec : ∀ x y st st',
  st X = x → st Y = y → st =[ XtimesYinZ ]=> st' →
  st' Z = x * y ∧ st' X = x ∧ st' Y = y.
Proof.
  intros x y st st' stx sty H.
  inversion H. split; try split; unfold t_update; simpl.
  - simpl in H4.
    subst x. subst y. symmetry. assumption.
  - assumption.
  - assumption.
Qed.


Definition loop : com :=
  WHILE true DO SKIP END.

Theorem loop_never_stops : ∀st st', ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef
           eqn:Heqloopdef.
  induction contra; try inversion Heqloopdef.
  - subst b. simpl in H. discriminate H.
  - subst b. subst c. apply IHcontra2. assumption.
Qed.

Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP     => true
  | _ ::= _  => true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END => false
  end.
Close Scope imp_scope.

Inductive no_whilesR: com → Prop :=
| SkipNoWhile : no_whilesR SKIP
| AssNoWhile : ∀ id exp, no_whilesR (id ::= exp) 
| SeqNoWhile : ∀ c d,
    no_whilesR c → no_whilesR d → no_whilesR (c ;; d)
| IfNoWhile : ∀ b t f,
    no_whilesR t → no_whilesR f → no_whilesR (TEST b THEN t ELSE f FI)
.


Lemma no_whiles_R : ∀ c, no_whiles c = true → no_whilesR c.
Proof.
  intros. induction c; try constructor; simpl in H;
  try apply andb_prop in H as [nwt1 nwt2];
  try apply IHc1; try apply IHc2;
  try assumption.
  inversion H.
Qed.

Lemma R_no_whiles : ∀ c, no_whilesR c → no_whiles c = true.
Proof.
  intros. induction H; simpl;
  try rewrite IHno_whilesR1; try rewrite IHno_whilesR2;
  try reflexivity.
Qed.

Theorem no_whiles_eqv:
   ∀c, no_whiles c = true ↔ no_whilesR c.
Proof.
  intros. split; solve [apply no_whiles_R | apply R_no_whiles].
Qed.

Theorem no_whiles_terminate:
  ∀ c, no_whilesR c → ∀st, ∃ st', st =[ c ]=> st'.
Proof.
  intros c H.
  induction H; intros.
  - exists st. constructor.
  - exists (id !-> aeval st exp ; st).
    constructor. reflexivity.
  - assert (∃ st', st =[ c ]=> st')
      as [st1 P1] by apply IHno_whilesR1.
    assert (∃ st', st1 =[ d ]=> st')
      as [st2 P2] by apply IHno_whilesR2.
    exists st2. apply E_Seq with (st' := st1); assumption.
  - destruct (beval st b) eqn: E.
    + assert (∃ st', st =[ t ]=> st')
        as [st' P] by apply IHno_whilesR1.
      exists st'. apply E_IfTrue ; assumption.
    + assert (∃ st', st =[ f ]=> st')
        as [st' P] by apply IHno_whilesR2.
      exists st'. apply E_IfFalse; assumption.
Qed.

