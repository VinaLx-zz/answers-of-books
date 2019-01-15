Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = 10 * 12.
Proof. simpl. reflexivity. Qed.

Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | O, O       => false
  | O, S m'    => true
  | S n', S m' => ltb n' m'
  | S n', O    => false
  end.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o nm mo.
  rewrite -> nm.
  rewrite -> mo.
  reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m msn.
  simpl.
  rewrite <- msn.
  reflexivity.
Qed.

