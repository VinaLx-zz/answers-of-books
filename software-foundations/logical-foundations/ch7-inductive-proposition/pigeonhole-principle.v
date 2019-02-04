Require Import Utf8.
Require Import List.
Import ListNotations.

Theorem all_in_in_tail :
  ∀ {X : Type} {x : X} {xs : list X} (P : X → Prop),
  (∀ x' : X, In x' (x :: xs) → P x') → (∀ x' : X, In x' xs → P x').
Proof.
  intros X x xs P all_in_cons x' in_tail.
  apply all_in_cons.
  simpl. right. assumption.
Qed.

Lemma in_split : ∀ (X:Type) (x:X) (l:list X),
  In x l → ∃ l1 l2, l = l1 ++ x :: l2.
Proof.
  induction l as [| h t IH]; intros; simpl.
  - simpl in H. contradiction.
  - simpl in H. destruct H as [xh | x_in_t].
    + exists []. exists t. rewrite xh. reflexivity.
    + apply IH in x_in_t as [l1 [l2 t_l1_x_l2]].
      exists (h :: l1). exists l2. simpl. rewrite t_l1_x_l2. reflexivity.
Qed.

Inductive repeats {X:Type} : list X → Prop :=
  | rep_in : ∀ (x : X) (xs : list X), In x xs → repeats (x :: xs)
  | rep_cons : ∀ (x : X) (xs : list X), repeats xs → repeats (x :: xs)
.

Theorem split_in : ∀ {X : Type} {x : X} {xs xs1 xs2 : list X},
  xs = xs1 ++ x :: xs2 → In x xs.
Proof.
  intros until xs1. generalize dependent xs.
  induction xs1 as [| h1 t1 IH]; simpl; intros.
  - destruct xs as [| h t].
    + discriminate H.
    + inversion H. simpl. left. reflexivity.
  - destruct xs as [| h t].
    + discriminate H.
    + inversion H.
      set (ih := IH t xs2 H2).
      simpl. right. rewrite <- H2. assumption.
Qed.

Theorem match_or_in_split : ∀ {X : Type} {x y : X} {l l1 l2 : list X},
  l = l1 ++ x :: l2 → In y l → y = x ∨ In y (l1 ++ l2).
Proof.
  induction l as [| h t IH]; simpl; intros.
  { contradiction. }
  destruct H0 as [hy | y_in_t].
  - destruct l1 as [| h1 t1].
    + simpl in H. inversion H. left. rewrite <- hy. rewrite <- H1. reflexivity.
    + right. simpl. left. simpl in H.
      inversion H. rewrite <- H1. rewrite <- hy. reflexivity.
  - destruct l1 as [| h1 t1]; simpl in H.
    + inversion H. simpl. right. rewrite <- H2. assumption.
    + inversion H. simpl.
      set (ih := IH t1 l2 H2 y_in_t).
      destruct ih. left. assumption. right. right. assumption.
Qed.


Theorem in_after_app : ∀ {X : Type} {x : X} {xs : list X},
  In x xs → (∀ ys : list X, In x (ys ++ xs)).
Proof.
  induction ys as [| h t IH].
  - simpl. assumption.
  - simpl. right. apply IH.
Qed.

Theorem in_insert : ∀ {X : Type} {x y : X} {l1 l2 : list X},
  In x (l1 ++ l2) → In x (l1 ++ y :: l2).
Proof.
  induction l1 as [| h t IH]; simpl; intros.
  - right. assumption.
  - destruct H.
    + left. assumption.
    + right. apply IH. assumption.
Qed.

Theorem length_cons_lt : ∀ {X : Type} {x : X} {xs : list X},
  length xs < length (x :: xs).
Proof.
  intros. simpl.
  unfold lt. apply le_n_S. constructor.
Qed.

Theorem length_insert_lt : ∀ {X : Type} {x : X} {xs ys : list X},
  S (length (xs ++ ys)) = length (xs ++ x :: ys).
Proof.
  intros. induction xs as [| h t IH]; simpl.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.


(*
  If `y` is in `xs` from which `x` is removed,
  the decision that which `x` is removed doesn't matter.
*)
Theorem split_in_consistent : ∀ {X : Type} {x y : X}
  {xs xs1 xs2 xs3 xs4 : list X},
  xs = xs1 ++ x :: xs2 → In y (xs1 ++ xs2) →
  xs = xs3 ++ x :: xs4 → In y (xs3 ++ xs4).
Proof.
  induction xs as [| h t IH]; simpl; intros xs1 xs2 xs3 xs4 xs12 H xs34.
  (* impossible case *)
  - destruct xs1; simpl in xs12; discriminate xs12.
  - destruct xs1 as [| h1 t1];
    simpl in xs12; simpl in xs34; simpl in H.
    + destruct xs3 as [| h3 t3] 
      ; inversion xs12; inversion xs34; simpl.
      { rewrite <- H4. rewrite H2. assumption. }
      { rewrite H2 in H4.
        set (H5 := match_or_in_split H4 H).
        rewrite <- H3. rewrite H1. destruct H5.
        - left. symmetry. assumption.
        - right. assumption. }
    + destruct xs3 as [| h3 t3]; destruct H as [h1y | y_in_t1_xs2] 
      ; inversion xs12; inversion xs34; simpl.
      { rewrite <- H3. rewrite H1.
        rewrite <- h1y. rewrite <- H2. rewrite <- H0.
        apply in_after_app. simpl. left. reflexivity. }
      { rewrite <- H3. rewrite H1. apply in_insert. assumption. }
      { left. rewrite <- H2. rewrite H0. rewrite h1y. reflexivity. }
      { set (ih := IH t1 xs2 t3 xs4 H1 y_in_t1_xs2 H3).
        right. assumption. }
Qed.

(*
  For any pair of proofs of membership. Either:
   - Two membership proofs are the same.
   - Removing one of the elements from list doesn't affect the other membership.
*)
Theorem match_or_split : ∀ {X : Type} {ys : list X} {x y : X}
  (ix : In x ys) (iy : In y ys),
  x = y ∨ (∃ ys1 ys2, ys = ys1 ++ y :: ys2 ∧ In x (ys1 ++ ys2)).
Proof.
  induction ys as [| h t IH]; intros.
  (* impossible case *)
  - simpl in ix. contradiction.
  - simpl in ix. simpl in iy.
    (* we discuss four possible cases of both memberships and try to yield
       corresponding result, which is straightforward *)
    destruct ix as [hx | in_x_t]; destruct iy as [hy | in_y_t].
    + left. rewrite <- hx. rewrite <- hy. reflexivity.
    + right. apply in_split in in_y_t as [t1 [t2 t_t1_y_t2]].
      exists (h :: t1). exists t2. split; simpl.
      * rewrite t_t1_y_t2. reflexivity.
      * left. assumption.
    + right. exists []. exists t. split; simpl.
      rewrite hy. reflexivity. assumption.
    + set (ih := IH x y in_x_t in_y_t).
      destruct ih as [xy | [t1 [t2 [t_t1_y_t2 x_in_t1_t2]]]].
      { left. assumption. }
      { right. exists (h :: t1). exists t2. simpl. split.
        - rewrite t_t1_y_t2. reflexivity.
        - right. assumption. }
Qed.

(*
For all `xs` being a subset of `ys`, if `y` is a member of `ys`. Either:
  - `y` is also in `xs`
  - Removing `y` from `ys` doesn't affect the fact that
    `xs` is still a subset of `ys`.
*)
Theorem pigeonhole' : ∀ {X : Type} (xs : list X)
  {y : X} {ys : list X} (y_in_ys : In y ys),
  (∀ x : X, In x xs → In x ys) →
  In y xs ∨
  (∃ ys1 ys2, ys = ys1 ++ y :: ys2 ∧ (∀ x : X, In x xs → In x (ys1 ++ ys2))).
Proof.
  intros until xs. induction xs as [| h t]; intros.
  (* trivial base case when `xs` is empty *)
  - right.
    apply in_split in y_in_ys as [y1 [y2 Eq]].
    exists y1. exists y2. split. assumption. intros. contradiction.
  - assert (In h ys) as h_in_ys. { apply H. simpl. left. reflexivity. }
    set (test_result := match_or_split h_in_ys y_in_ys).
    destruct test_result as [hy | [ys1 [ys2 [ys_y1_y_y2 h_in_ys1_ys2]]]].
    (* `h = y` means `h` is just the element we want *)
    + left. simpl. left. assumption.

    (* otherwise induction hypothesis is applied to check the rest of xs *)
    + set (H0 := all_in_in_tail (λ x, In x ys) H). simpl in H0.
      set (iht := IHt y ys y_in_ys H0).
      (* a match is found in the tail *)
      destruct iht. { left. simpl. right. assumption. }

      (* otherwise, we apply the split result of induction hypothesis *)
      right.
      destruct H1 as [ys1' [ys2' [ys_y1'_y_y2' h_in_ys1'_ys2']]].
      exists ys1'. exists ys2'.
      split. { assumption. }

      (* final proof for subset relation *)
      intros x x_in_ht.
      destruct x_in_ht as [xh | x_in_t].
      * rewrite <- xh.
        (* unfortunately, although we are able to prove the membership of `h`
           w.r.t our current split choice. It's not trivial to show any split
           choice makes no difference when talking about membership of other
           elements, so we have to apply another helper proof here *)
        set (R := split_in_consistent ys_y1_y_y2 h_in_ys1_ys2 ys_y1'_y_y2').
        assumption.
      * apply h_in_ys1'_ys2'. assumption.
Qed.

(* After pigeonhole' is defined, the proof is straightforward. *)
Lemma pigeonhole_principle: ∀ (X:Type) (xs ys : list X),
   (∀ x, In x xs → In x ys) → length ys < length xs → repeats xs.
Proof.
  induction xs as [| x xs' IH]; intros ys H ly_lt_lx; simpl.
  (* impossible case *)
  - unfold lt in ly_lt_lx. simpl in ly_lt_lx. inversion ly_lt_lx.
  (*
   extract the `h` (head) in `xs`, map its membership in `xs` to membership
   in `ys`, and check if there's other element in `t`(tail) of `xs`, whose
   "image" in `ys` share the same membership as image of `h`...
   (what pigeonhole' do)
   *)
  - assert (In x ys) as x_in_ys. { apply H. simpl. left. reflexivity. } 
    set (Hxs' := all_in_in_tail (λ x, In x ys) H). simpl in Hxs'.
    set (duplicate_or_split := pigeonhole' xs' x_in_ys Hxs').
    destruct duplicate_or_split as [duplicate | [ys1 [ys2 [ys_ys1x2 H']]]].
    (* ... if so, then we find a base case of repeat *)
    + apply rep_in. apply duplicate.
    (* ... if not, we remove that element from `y` (`pigeonhole'` does this),
       and apply the induction hypothesis *)
    + apply rep_cons. apply IH with (ys1 ++ ys2).
      (* subset relation is obtained from `pigeonhole'` *)
      * assumption.
      (* trivial proof of length relation being preserved *)
      * unfold lt. unfold lt in ly_lt_lx.
        rewrite (@length_insert_lt X x ys1 ys2).
        rewrite <- ys_ys1x2.
        simpl in ly_lt_lx. apply le_S_n. assumption.
Qed.

