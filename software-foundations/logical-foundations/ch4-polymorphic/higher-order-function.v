Require Import Nat.
Require Import List.
Require Import Bool.
Import ListNotations.

(* filter *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => negb (x <=? 7) && even x) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X)
                   : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* map *)

Theorem map_app_distr : forall (X Y : Type) (f : X -> Y) (xs ys : list X), map f (xs ++ ys) = map f xs ++ map f ys.
Proof.
  intros.
  induction xs as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite map_app_distr.
    simpl. rewrite IH.
    reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y) :=
    match l with
    | [] => []
    | h :: t => f h ++ flat_map f t
    end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(* additional exercises *)

(* the implementation in software foundation is equivalent fold_right*)
(* so I just replace it with fold_right and adjust the order of arguments*)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold_right (fun _ n => S n) 0 l.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) : list X -> list Y :=
  fold_right (fun x ys => f x :: ys) [].

Theorem fold_map_correct : forall X Y (l : list X) (f : X -> Y),
  fold_map f l = map f l.
Proof.
  intros.
  induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := let (x, y) := p in f x y.

Theorem uncurry_curry : forall (X Y Z : Type)
  (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  unfold prod_curry.
  unfold prod_uncurry.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
  (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p.
  unfold prod_uncurry.
  unfold prod_curry.
  reflexivity.
Qed.


