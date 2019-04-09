Require Import Peano.

Theorem plus_n_n_injective : forall n m : nat,
     n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n']; intros m H.
  - destruct m.
    + reflexivity.
    + simpl in H. discriminate H.
  - destruct m; simpl in H.
    + discriminate H.
    + repeat rewrite <- plus_n_Sm in H.
      injection H. intros.
      apply IHn' in H0. rewrite H0.
      reflexivity.
Qed.

