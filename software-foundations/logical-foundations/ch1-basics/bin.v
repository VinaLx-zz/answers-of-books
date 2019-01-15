Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m: bin) : bin :=
    match m with
    | Z => B Z
    | A b' => B b'
    | B b' => A (incr b')
    end.

Fixpoint bin_to_nat (m: bin) : nat :=
    match m with
    | Z => 0
    | A b' => 2 * (bin_to_nat b')
    | B b' => S (2 * (bin_to_nat b'))
    end.

Example test_bin_1: bin_to_nat Z = 0.
Proof. reflexivity. Qed.

Example test_bin_2: bin_to_nat (incr Z) = 1.
Proof. reflexivity. Qed.

Example test_bin_3:
    bin_to_nat (incr (incr (incr (incr (incr Z))))) = 5.
Proof. reflexivity. Qed.
