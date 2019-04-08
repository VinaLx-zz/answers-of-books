Require Import Utf8.
Require Import State.
Require Import String.
Require Import List.
Require Import Nat.
Import ListNotations.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Definition stack_op (stack : list nat) (op : nat → nat → nat): list nat :=
  match stack with
  | a :: b :: tail => op b a :: tail
  | otherwise => stack
  end
.

Definition s_execute_1 (st : state) (stack : list nat) (instr : sinstr)
    : list nat :=
  match instr with
  | SPush n => n :: stack
  | SLoad x => st x :: stack
  | SPlus => stack_op stack add
  | SMinus => stack_op stack minus
  | SMult => stack_op stack mult
  end
.

Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr)
                 : list nat :=
  match prog with
  | [] => stack
  | i :: prog => s_execute st (s_execute_1 st stack i) prog
  end
.

Example s_execute1 :
  s_execute empty_st [] [SPush 5; SPush 3; SPush 1; SMinus] = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
  s_execute (X !-> 3) [3;4] [SPush 4; SLoad X; SMult; SPlus] = [15; 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [ SPush n  ]
  | AId id => [ SLoad id ]
  | APlus  l r => s_compile l ++ s_compile r ++ [ SPlus  ]
  | AMinus l r => s_compile l ++ s_compile r ++ [ SMinus ]
  | AMult  l r => s_compile l ++ s_compile r ++ [ SMult  ]
  end
.

Lemma s_execute_app : ∀ st init p1 p2,
  s_execute st init (p1 ++ p2) = s_execute st (s_execute st init p1) p2.
Proof.
  intros. generalize dependent init.
  induction p1; intros.
  - reflexivity.
  - simpl. rewrite IHp1. reflexivity.
Qed.

Theorem s_compile_correct' : ∀ st e init,
  s_execute st init (s_compile e) = aeval st e :: init.
Proof.
  induction e; intros; try reflexivity;
  simpl; repeat rewrite s_execute_app;
  rewrite IHe1; rewrite IHe2; simpl; reflexivity.
Qed.

Theorem s_compile_correct : ∀(st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  apply s_compile_correct'.
Qed.
