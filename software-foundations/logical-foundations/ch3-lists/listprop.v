Require Import List.
Require Import Nat.
Require Import Bool.

Import ListNotations.

Definition natlist := list nat.

Theorem nil_app : forall l:natlist, [] ++ l = l.
Proof. reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

(* definition above *)

(* List Exercies, Part 1 *)

Theorem app_nil_r : forall l : natlist, l ++ [] = l.
Proof.
  induction l as [| h t Eq].
  - reflexivity.
  - simpl. rewrite -> Eq. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 Eq1].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite -> Eq1.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [| h t Eq].
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite -> Eq.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite <- (app_assoc l2 l3 l4).
  rewrite <- (app_assoc l1 (l2 ++ l3) l4).
  rewrite <- (app_assoc l1 l2 l3).
  reflexivity.
Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | []         => []
  | O     :: t => nonzeros t
  | (S n) :: t => S n :: nonzeros t
  end.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| h1 t1 Eq1].
  - reflexivity.
  - destruct h1.
    + simpl. rewrite -> Eq1. reflexivity.
    + simpl. rewrite -> Eq1. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | [], [] => true
    | [], h :: t => false
    | h :: t, [] => false
    | h1 :: t1, h2 :: t2 => (h1 =? h2) && eqblist t1 t2
    end.

Example test_eqblist1 : (eqblist nil nil = true).
Proof. reflexivity. Qed.
 
Example test_eqblist2 : eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3 : eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Require Import EqNat.

Theorem eqblist_refl : forall l: natlist,
  true = eqblist l l.
Proof.
  induction l as [| h t Eq].
  - reflexivity.
  - simpl.
    rewrite <- Eq.
    rewrite <- (beq_nat_refl h).
    reflexivity.
Qed.

Theorem snoc_not_empty : forall (x : nat) (xs : natlist),
    [] = xs ++ [x] -> False.
Proof.
    intros x xs eq.
    induction xs as [| xh xs' H].
    - simpl in eq. inversion eq.
    - simpl in eq. inversion eq.
Qed.

Inductive natlist_pair : natlist -> natlist -> Type :=
| nils : natlist_pair [] []
| l_cons : forall (x : nat) (xs : natlist), natlist_pair (x :: xs) []
| r_cons : forall (y : nat) (ys : natlist), natlist_pair [] (y :: ys)
| conses : forall (x y : nat) (xs ys : natlist),
    natlist_pair xs ys -> natlist_pair (x :: xs) (y :: ys).

Fixpoint to_natlist_pair (xs ys : natlist) : natlist_pair xs ys :=
    match xs, ys with
    | [], [] => nils
    | x :: xs, [] => @l_cons x xs
    | [], y :: ys => @r_cons y ys
    | x :: xs', y :: ys' => @conses x y xs' ys' (to_natlist_pair xs' ys')
    end.

Theorem list_snoc_eq : forall (xs ys : natlist) (x y : nat),
    xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y.
Proof.
    intros xs ys x y eq.
    induction (to_natlist_pair xs ys).
    - simpl in eq. inversion eq. split; reflexivity.
    - simpl in eq. inversion eq. symmetry in H1.
      apply snoc_not_empty in H1. contradiction.
    - simpl in eq. inversion eq.
      apply snoc_not_empty in H1. contradiction.
    - simpl in eq. inversion eq.
      apply IHn in H1. destruct H1 as [xsys xy]. split.
      + rewrite xsys. reflexivity.
      + assumption.
Qed.

Theorem rev_inject : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 rev_eq.
  induction (to_natlist_pair l1 l2).
  - reflexivity.
  - simpl in rev_eq. symmetry in rev_eq. 
    apply snoc_not_empty in rev_eq. contradiction.
  - simpl in rev_eq.
    apply snoc_not_empty in rev_eq. contradiction.
  - simpl in rev_eq. apply list_snoc_eq in rev_eq.
    destruct rev_eq as [rxsrys xy].
    apply IHn in rxsrys.
    rewrite rxsrys. rewrite xy. reflexivity.
Qed.

