Require Export Utf8.

Inductive tm : Type :=
| C : nat → tm
| P : tm → tm → tm.

Fixpoint evalF (t : tm) : nat :=
  match t with
  | C n => n
  | P lhs rhs => evalF lhs + evalF rhs
  end
.

Inductive value : tm → Prop :=
| v_const : ∀ n, value (C n)
.

Reserved Notation "t '==>' n" (at level 50, left associativity).

Inductive eval : tm → nat → Prop :=
| E_Const : ∀ n, C n ==> n
| E_Plus : ∀ t1 t2 n1 n2,
    t1 ==> n1 → t2 ==> n2 → P t1 t2 ==> (n1 + n2)
where "t '==>' n" := (eval t n).

Reserved Notation " t '-->' t'" (at level 40).

Inductive step : tm → tm → Prop :=
| ST_PlusConstConst : ∀ n1 n2,
    P (C n1) (C n2) --> C (n1 + n2)
| ST_Plus1 : ∀ t1 t1' t2,
      t1    -->   t1' →
    P t1 t2 --> P t1' t2
| ST_Plus2 : ∀ n t t',
            t -->         t' →
    P (C n) t --> P (C n) t'
where "t '-->' t'" := (step t t').

(* ex. test_step_2 *)
Example test_step_2 :
  P (C 0) (P (C 2) (P (C 0) (C 3))) -->
  P (C 0) (P (C 2) (C (0 + 3))).
Proof.
  apply ST_Plus2.
  apply ST_Plus2.
  apply ST_PlusConstConst.
Qed.

