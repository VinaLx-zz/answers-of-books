Require Import Utf8.
Require Import State.
Require Import Nat.

Fixpoint beval_ss (st : state) (expr : bexp): bool :=
  match expr with
  | BTrue  => true
  | BFalse => false
  | BEq l r => aeval st l =?  aeval st r
  | BLe l r => aeval st l <=? aeval st r
  | BNot e => negb (beval st e) 
  | BAnd l r =>
    match beval st l with
    | true  => beval st r
    | false => false
    end
  end
.

Lemma beval_short_circuit_equiv : ∀ st expr, beval st expr = beval_ss st expr.
Proof.
  induction expr; try reflexivity.
Qed.

