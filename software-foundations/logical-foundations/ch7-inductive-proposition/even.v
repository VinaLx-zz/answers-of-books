Require Import PeanoNat.
Import Nat.

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n : nat, even n -> even (S (S n)).

Theorem ev_double : forall n, even (double n).
Proof.
  unfold double. induction n as [| n' IH].
  - simpl. apply ev_0.
  - rewrite <- plus_n_Sm. simpl.
    apply ev_SS. apply IH.
Qed.

Theorem SSSSev_even : forall n, even (S (S (S (S n)))) -> even n.
Proof.
  intros n ev.
  inversion ev as [| n' ev' Eq].
  inversion ev' as [| n'' ev'' Eq'].
  apply ev''.
Qed.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intro even5.
  inversion even5 as [| n3 even3 n_eq_3].
  inversion even3 as [| n1 even1 n_eq_1].
  inversion even1.
Qed.

Theorem ev_sum : forall {n m : nat}, even n -> even m -> even (n + m).
Proof.
  intros n m even_n. generalize dependent m.
  induction even_n as [| n' even_n' IH].
  - intros. simpl. assumption.
  - intros m even_m. simpl.
    apply IH in even_m.
    apply ev_SS. assumption.
Qed.

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum : forall n m : nat, even' n -> even' m -> even' (n + m).

Theorem even_even' : forall n : nat, even n -> even' n.
Proof.
  intros n even_n.
  induction even_n as [| n' even_n' IH].
  - apply even'_0.
  - assert (S (S n') = 2 + n') as E by reflexivity.
    rewrite E.
    apply even'_sum. apply even'_2. apply IH.
Qed.

Theorem even'_even : forall n : nat, even' n -> even n.
Proof.
  intros n even'_n.
  induction even'_n as [ | | x y even'_x IHx even'_y IHy].
  - apply ev_0.
  - apply ev_SS. apply ev_0.
  - apply ev_sum. apply IHx. apply IHy.
Qed.

Theorem even'_ev : forall n : nat, even' n <-> even n.
Proof.
  intros n. split.
  - apply even'_even.
  - apply even_even'.
Qed.

Theorem ev_ev__ev : forall n m : nat, even (n + m) -> even n -> even m.
Proof.
  intros n m even_nm even_n.
  generalize dependent m.
  induction even_n as [| n' even_n' IH].
  - intros. assumption.
  - intros. simpl in even_nm.
    inversion even_nm as [| n'm even_n'm E].
    apply IH in even_n'm.
    apply even_n'm.
Qed.

Theorem ev_plus_plus : forall n m p : nat,
  even (n + m) -> even (n + p) -> even (m + p).
Proof.
  intros n m p even_nm even_np.
  set (even_nmnp := ev_sum even_nm even_np).
  rewrite add_assoc in even_nmnp.
  rewrite <- (add_assoc n m n) in even_nmnp.
  rewrite <- (add_comm n m) in even_nmnp.
  rewrite (add_assoc n n m) in even_nmnp.
  rewrite <- add_assoc in even_nmnp.
  apply ev_ev__ev with (n := n + n).
  - apply even_nmnp.
  - assert (n + n = double n) as E by reflexivity.
    rewrite E.
    apply ev_double.
Qed.

