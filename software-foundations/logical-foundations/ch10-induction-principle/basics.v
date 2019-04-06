Require Import Utf8.
Require Import Nat.

Theorem plus_1_r': ∀ n, n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IH. simpl.
    rewrite IH. reflexivity.
Qed.

Definition PlusAssoc (a : nat) := ∀ b c, a + b + c = a + (b + c).
Definition PlusComm  (a : nat) := ∀ b  , a + b     = b + a.

Theorem plus_assoc' : ∀ a, PlusAssoc a.
Proof.
  apply nat_ind; unfold PlusAssoc.
  - intros. reflexivity.
  - intros. simpl. rewrite H. reflexivity.
Qed.
  
Theorem plus_comm' : ∀ a, PlusComm a.
Proof.
  apply nat_ind; unfold PlusComm.
  - intros. rewrite <- plus_n_O. reflexivity.
  - intros. simpl. rewrite <- plus_n_Sm. rewrite H. reflexivity.
Qed.
  
