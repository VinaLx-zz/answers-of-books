Require Import List.
Require Import Nat.

Import ListNotations.

Definition bag := list nat.

Fixpoint count (v: nat) (s: bag) : nat :=
    match s with
    | [] => 0
    | h :: t => if v =? h then S (count v t) else count v t
    end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum (b1 : bag) (b2 : bag) : bag := app b1 b2. 

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
    negb (count v s =? 0).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | [] => []
    | h :: t => if h =? v then t else h :: remove_one v t
    end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | [] => []
    | h :: t => if h =? v
        then remove_all v t
        else h :: remove_all v t
    end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
    | [] => true
    | h :: t => member h s2 && subset t (remove_one h s2)
    end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

(* List Exercies, Part 2 *)

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof. reflexivity. Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (l : bag),
  (count 0 (remove_one 0 l)) <=? (count 0 l) = true.
Proof.
  induction l as [| h t H].
  - reflexivity.
  - simpl. destruct h.
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite -> H. reflexivity.
Qed.

Theorem count_sum : forall (n: nat) (xs ys: bag),
    count n xs + count n ys = count n (xs ++ ys).
Proof.
    intros n xs ys.
    induction xs as [| hx tx Hx].
    - reflexivity.
    - destruct (n =? hx) as [|] eqn:n_eq_h.
      + simpl. rewrite -> n_eq_h.
        simpl. rewrite -> Hx.
        reflexivity.
      + simpl. rewrite -> n_eq_h.
               rewrite -> Hx.
        reflexivity.
Qed.

