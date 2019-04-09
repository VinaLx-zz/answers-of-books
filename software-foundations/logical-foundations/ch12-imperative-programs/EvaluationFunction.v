(*
  Sources in this file is the sample solution of chapter 14 of logical
  foundation: "evaluation function". The source file is placed here since the
  content of chapter 14 is closely related to the content of chapter 12:
  "imperative programs".
*)

Require Import Utf8.
Require Import State.
Require Import String.
Require Import TotalMap.

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Open Scope imp_scope.

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O    => None
  | S i' =>
    match c with
    | SKIP     => Some st
    | l ::= a1 => Some (l !-> aeval st a1 ; st)
    | c1 ;; c2 =>
        LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
        then ceval_step st c1 i'
        else ceval_step st c2 i'
    | WHILE b1 DO c1 END =>
        if (beval st b1)
        then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
        else Some st
    end
  end.
Close Scope imp_scope.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Definition pup_to_n : com :=
  Y ::= 0 ;; 
  WHILE (¬ X = 0) DO
    Y ::= Y + X ;;
    X ::= X - 1
  END.

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

Definition peven : com :=
  Z ::= X ;;
  WHILE 2 ≤ Z DO
    Z ::= Z - 2
  END
.

Example peven_test_1 : test_ceval (X !-> 0) peven = Some (0, 0, 0).
Proof. reflexivity. Qed.

Example peven_test_2 : test_ceval (X !-> 1) peven = Some (1, 0, 1).
Proof. reflexivity. Qed.

Example peven_test_3 : test_ceval (X !-> 4) peven = Some (4, 0, 0).
Proof. reflexivity. Qed.

Example peven_test_4 : test_ceval (X !-> 11) peven = Some (11, 0, 1).
Proof. reflexivity. Qed.

Theorem ceval_step__ceval: ∀c st st',
  (∃i, ceval_step st c i = Some st') → st =[ c ]=> st'.
Proof.
  intros c st st' [i H].
  generalize dependent st.
  generalize dependent st'.
  generalize dependent c.
  induction i; intros. simpl. inversion H.
  destruct c; simpl in H. 
  - inversion H as [Hst]. apply E_Skip.
  - inversion H as [Hst]. apply E_Ass. reflexivity.
  - destruct (ceval_step st  c1 i) as [st1 |] eqn: E1; try
    destruct (ceval_step st1 c2 i) as [st2 |] eqn: E2; inversion H as [Hst].
    subst st2. apply E_Seq with st1; apply IHi; assumption.
  - destruct (beval st b) eqn: EB.
    1: apply E_IfTrue. 3: apply E_IfFalse.
    all: try apply IHi; assumption.
  - destruct (beval st b) eqn: EB.
    + destruct (ceval_step st  c i) as [st1 |] eqn: E1; try
      destruct (ceval_step st1 (WHILE b DO c END) i) as [st2 |] eqn: E2;
      inversion H as [Hst]. subst st2.
      apply E_WhileTrue with st1. exact EB.
      all: (apply IHi; assumption).
    + inversion H. subst st.
      apply E_WhileFalse. exact EB.
Qed.

Require Import Omega.

(* Proof is given by the textbook *)
Axiom ceval_step_more: ∀i1 i2 st st' c,
  i1 ≤ i2 → ceval_step st c i1 = Some st' → ceval_step st c i2 = Some st'.

Theorem ceval__ceval_step: ∀ c st st',
  st =[ c ]=> st' → ∃ i, ceval_step st c i = Some st'.
Proof.
  intros c st st' H. induction H;
  try
  ( destruct IHceval1 as [n1 Hst1]
  ; destruct IHceval2 as [n2 Hst2]
  ; apply ceval_step_more with (i2 := n1 + n2) in Hst1
  ; apply ceval_step_more with (i2 := n1 + n2) in Hst2
  );
  try omega;
  try destruct IHceval as [n Hst].
  - exists 1. reflexivity.
  - exists 1. simpl. rewrite H. reflexivity.
  - exists (S (n1 + n2)). simpl. 
    rewrite Hst1. exact Hst2.
  - exists (S n). simpl. rewrite H. exact Hst.
  - exists (S n). simpl. rewrite H. exact Hst.
  - exists 1. simpl. rewrite H. reflexivity.
  - exists (S (n1 + n2)). simpl. rewrite H.
    rewrite Hst1. exact Hst2.
Qed.

Theorem ceval_and_ceval_step_coincide: ∀ c st st',
  st =[ c ]=> st' ↔ ∃ i, ceval_step st c i = Some st'.
Proof.
  intros. split.
  apply ceval__ceval_step. apply ceval_step__ceval.
Qed.
