Require Import Nat.

Definition natoption := option nat.

Inductive id : Type :=
| Id (n : nat).

Definition eqb_id (x1 x2 : id) : bool :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  destruct x as [n].
  induction n as [| n' IH].
  - reflexivity.
  - simpl. simpl in IH. rewrite <- IH. reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite <- eqb_id_refl. reflexivity.
Qed.

