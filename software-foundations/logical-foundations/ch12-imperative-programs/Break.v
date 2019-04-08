Require Import Utf8.
Require Import State.
Require Import String.
Require Import TotalMap.

Inductive com : Type :=
| CSkip
| CBreak 
| CAss (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Notation "'SKIP'" := CSkip.
Notation "'BREAK'" := CBreak.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

Inductive result : Type :=
  | SContinue
  | SBreak.
Reserved Notation "st '=[' c ']=>' st' '/' s"
         (at level 40, st' at next level).

Inductive CEval : com → state → state → result → Prop :=
| ESkip  : ∀ st, st =[ SKIP ]=> st / SContinue
| EBreak : ∀ st, st =[ BREAK ]=> st / SBreak
| EAss  : ∀ st id expr n,
    aeval st expr = n →
    st =[ id ::= expr ]=> (id !-> n ; st) / SContinue
| ESeq1 : ∀ st c1 st' c2,
    st  =[    c1    ]=> st' / SBreak →
    st  =[ c1 ;; c2 ]=> st' / SBreak
| ESeq2 : ∀ st1 c1 st2 c2 st3 s,
    st1 =[    c1    ]=> st2 / SContinue →
    st2 =[    c2    ]=> st3 / s         →
    st1 =[ c1 ;; c2 ]=> st3 / s
| EIfTrue : ∀ st cond ct st' s cf,
    beval st cond = true →    st =[ ct ]=> st' / s →
    st =[ TEST cond THEN ct ELSE cf FI ]=> st' / s
| EIfFalse : ∀ st cond ct cf st' s,
    beval st cond = false →   st =[ cf ]=> st' / s →
    st =[ TEST cond THEN ct ELSE cf FI ]=> st' / s
| EWhileStop : ∀ st cond c,
    beval st cond = false →
    st =[ WHILE cond DO c END ]=> st / SContinue
| EWhileContinue : ∀ st1 cond c st2 st3,
    beval st1 cond = true →
    st1 =[         c           ]=> st2 / SContinue →
    st2 =[ WHILE cond DO c END ]=> st3 / SContinue →
    st1 =[ WHILE cond DO c END ]=> st3 / SContinue
| EWhileBreak : ∀ st cond c st',
    beval st cond = true →
    st =[          c          ]=> st' / SBreak →
    st =[ WHILE cond DO c END ]=> st' / SContinue
where "st '=[' c ']=>' st' '/' s" := (CEval c st st' s).


Theorem break_ignore : ∀ c st st' s,
  st =[ BREAK ;; c ]=> st' / s → st = st'.
Proof.
  intros. inversion H.
  - inversion H5. reflexivity.
  - inversion H2.
Qed.

Theorem while_continue : ∀ b c st st' s,
  st =[ WHILE b DO c END ]=> st' / s → s = SContinue.
Proof.
  intros. inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : ∀b c st st',
  beval st b = true → st =[ c ]=> st' / SBreak →
  st =[ WHILE b DO c END ]=> st' / SContinue.
Proof.
  intros. apply EWhileBreak; assumption.
Qed.

Theorem while_break_true : ∀ b c st st',
  st =[ WHILE b DO c END ]=> st' / SContinue → beval st' b = true →
  ∃st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros. remember (WHILE b DO c END) as loop.
  induction H; inversion Heqloop; subst b; subst c0.
  - rewrite H in H0. inversion H0.
  - apply IHCEval2. reflexivity. assumption.
  - exists st. assumption.
Qed.

Theorem ceval_deterministic: ∀ c st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 →
     st =[ c ]=> st2 / s2 →
     st1 = st2 ∧ s1 = s2.
Proof.
  intros c. 
  induction c; intros st st1 st2 s1 s2 H1 H2.
  - inversion H1; inversion H2; subst st1 st2. split; reflexivity.
  - inversion H1; inversion H2; subst st1 st2. split; reflexivity.
  - inversion H1; inversion H2; subst n n0. split; reflexivity.
  - inversion H1; inversion H2.
    -- apply IHc1 with (st := st); assumption.
    -- assert (st1 = st4 ∧ SBreak = SContinue) as [_ contra]. 
        apply IHc1 with (st := st); assumption. inversion contra.
    -- assert (st3 = st2 ∧ SContinue = SBreak) as [_ contra].
        apply IHc1 with (st := st); assumption. inversion contra.
    -- apply IHc2 with (st := st3). assumption.
        assert (st3 = st6 ∧ SContinue = SContinue) as [H' _].
        + apply IHc1 with (st := st); assumption.
        + rewrite H'. assumption.
  - inversion H1; inversion H2; try congruence.
    -- apply IHc1 with (st := st); assumption.
    -- apply IHc2 with (st := st); assumption.
  - remember (WHILE b DO c END) as loop.
    induction H1; inversion Heqloop; inversion H2; try congruence;
    subst c0 c1 cond cond0 s2; try subst st4; try subst st6.
    -- split; reflexivity.
    -- apply IHCEval2. reflexivity.
       assert (st0 = st5 ∧ SContinue = SContinue) as [Hrw _].
       apply IHc with (st := st1); assumption. rewrite Hrw. assumption.
    -- assert (st0 = st2 ∧ SContinue = SBreak) as [_ contra].
       apply IHc with (st := st1); assumption. inversion contra.
    -- assert (st' = st0 ∧ SBreak = SContinue) as [_ contra].
       apply IHc with (st := st); assumption. inversion contra.
    -- assert (st' = st2 ∧ SBreak = SBreak) as [Hrw _].
       apply IHc with (st := st); assumption. rewrite Hrw. split; reflexivity.
Qed.

(*
  The last question involving 'for' loop, but for loop can be defined merely as
  a syntastic sugar of 'while' and ';;', so adding another definition seems
  unnecessary.
*)
Definition For (init : com) (cond : bexp) (iter : com) (body : com) :=
    init ;; WHILE cond DO body ;; iter END.
