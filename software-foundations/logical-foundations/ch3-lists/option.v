Require Import List.
Require Import Nat.
Import ListNotations.

Definition natlist := list nat.

Inductive natoption : Type :=
| Some (n : nat) : natoption
| None.

Definition hd_error (l : natlist) : natoption :=
    match l with
    | [] => None
    | h :: t => Some h
    end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | [] => default
    | h :: t => h
    end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros [| h t] default; reflexivity.
Qed.

