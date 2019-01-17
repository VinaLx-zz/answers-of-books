Inductive natprod: Type :=
| pair (first second : nat).

Notation "( x , y )" := (pair x y).

Definition fst (p: natprod) : nat :=
    match p with
    | (x, y) => x
    end.

Definition snd (p: natprod) : nat :=
    match p with
    | (x, y) => y
    end.

Definition swap_pair (p: natprod) : natprod :=
    match p with
    | (x, y) => (y, x)
    end.

Theorem snd_fst_is_swap : forall (p: natprod),
    (snd p, fst p) = swap_pair p.
Proof.
    destruct p.
    reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p: natprod),
    fst (swap_pair p) = snd p.
Proof.
    destruct p.
    reflexivity.
Qed.

