Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [| n' H].
    - reflexivity.
    - simpl. rewrite -> H. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  induction n as [| n' H].
    - reflexivity.
    - intros m. simpl.
      rewrite -> (H m).
      reflexivity.
Qed.

Theorem plus_n_O : forall n : nat,
  n = n + 0.
Proof.
  induction n as [| n' H].
    - reflexivity.
    - simpl. rewrite <- H. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n' H].
    - simpl. intros m.
      rewrite <- (plus_n_O m).
      reflexivity.
    - simpl. intros m.
      rewrite <- (plus_n_Sm m n').
      rewrite <- H.
      reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [| n' H].
    - reflexivity.
    - simpl. intros m p.
      rewrite -> (H m p).
      reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n,
  double n = n + n.
Proof.
  induction n as [| n' H].
    - reflexivity.
    - simpl.
      rewrite <- (plus_n_Sm n' n').
      rewrite <- H.
      reflexivity.
Qed.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  induction n as [| n' H].
    - reflexivity.
    - rewrite -> H.
      rewrite -> (negb_involutive (evenb n')).
      reflexivity.
Qed.
