Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import EqNat.

Require Import relation.

Inductive nostutter {X:Type} : list X → Prop :=
  | ns_nil : nostutter []
  | ns_single : forall (x : X), nostutter [x]
  | ns_cons : forall (x y : X) (xs : list X),
    x ≠ y → nostutter (y :: xs) → nostutter (x :: y :: xs)
.

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply beq_nat_false_iff; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. repeat constructor; apply beq_nat_false_iff; auto.
Qed.

Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. intro.
repeat match goal with
  h: nostutter _ |- _ => inversion h; clear h; subst
end.
contradiction H1; auto. Qed.

Inductive InOrderMerge {X : Type} : list X → list X → list X → Prop :=
  | m_nils : InOrderMerge [] [] []
  | m_cons_l : ∀ {x : X} {xs ys zs : list X},
    InOrderMerge xs ys zs → InOrderMerge (x :: xs) ys (x :: zs)
  | m_cons_r : ∀ {y : X} {xs ys zs : list X},
    InOrderMerge xs ys zs → InOrderMerge xs (y :: ys) (y :: zs)
.

Theorem all_in_in_tail :
  ∀ {X : Type} {x : X} {xs : list X} (P : X → Prop),
  (∀ x' : X, In x' (x :: xs) → P x') → (∀ x' : X, In x' xs → P x').
Proof.
  intros X x xs P all_in_cons x' in_tail.
  apply all_in_cons.
  simpl. right. assumption.
Qed.

Theorem filter_challenge : ∀ {X : Type} {p : X → bool} {xs ys : list X},
  (∀ {x : X}, In x xs → p x = true) → (∀ {y : X}, In y ys → p y = false) →
  (∀ zs : list X, InOrderMerge xs ys zs → filter p zs = xs).
Proof.
  intros X p xs ys xs_t ys_f zs merge.
  induction merge.
  - reflexivity.
  - simpl. cut (p x = true).
    + intros H. rewrite H.
      set (in_xs := all_in_in_tail (λ x, p x = true) xs_t).
      set (E := IHmerge in_xs ys_f).
      rewrite E. reflexivity.
    + apply xs_t. simpl. left. reflexivity.
  - simpl. cut (p y = false).
    + intros H. rewrite H.
      apply IHmerge. apply xs_t.
      set (in_ys := all_in_in_tail (λ y, p y = false) ys_f).
      apply in_ys.
    + apply ys_f. simpl. left. reflexivity.
Qed.

Inductive subseq {X : Type}: list X → list X → Prop :=
  | sub_nil : ∀ xs, subseq [] xs
  | sub_cons_r : ∀ (y : X) (xs ys : list X),
        subseq xs ys -> subseq xs (y :: ys)
  | sub_cons : ∀ (x : X) (xs ys : list X),
        subseq xs ys -> subseq (x :: xs) (x :: ys)
.

Theorem filter_subseq_longest :
  ∀ {X : Type} {p : X → bool} {xs ys : list X},
  subseq ys xs → (∀ {y : X}, In y ys → p y = true) →
  length ys ≤ length (filter p xs).
Proof.
  intros X p xs ys ss_ys_xs.
  induction ss_ys_xs as
    [| x ys xs' ss_ys_xs' IH | x ys' xs' ss_ys'_xs' IH]; intros; simpl.
  - apply O_le_n.
  - apply IH in H. destruct (p x).
    + simpl. apply le_S. assumption.
    + assumption.
  - set (H0 := all_in_in_tail (λ y, p y = true) H).
    apply IH in H0.
    simpl. destruct (p x) eqn: E. simpl.
    + apply le_n_S. assumption.
    + cut (p x = true).
      intros. rewrite E in H1. discriminate H1.
      apply H. simpl. left. reflexivity.
Qed.

Inductive Palindrome {X : Type} : list X → Prop :=
  | pal_nil : Palindrome []
  | pal_single : ∀ x : X, Palindrome [x]
  | pal_cat : ∀ {xs : list X} (x : X),
    Palindrome xs → Palindrome (x :: xs ++ [x])
.

Theorem app_rev_pal : ∀ {X : Type} {xs : list X},
  Palindrome (xs ++ rev xs).
Proof.
  induction xs as [| x xs' IH]; simpl.
  - constructor.
  - rewrite app_assoc. apply pal_cat. apply IH.
Qed.

Theorem rev_app_distr : ∀ {X : Type} {xs ys : list X},
  rev (xs ++ ys) = rev ys ++ rev xs.
Proof.
  induction xs as [| x xs' IH]; intros; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. rewrite IH. reflexivity.
Qed.

Theorem pal_rev_eq : ∀ {X : Type} {xs : list X},
  Palindrome xs → xs = rev xs.
Proof.
  intros X xs pal.
  induction pal as [ | | xs' x pal_xs' IH];
  [> .. | simpl; rewrite rev_app_distr; rewrite <- IH];
  reflexivity.
Qed.

Inductive ListConsSnocView {X : Type} : list X → Type :=
  | cs_nil : ListConsSnocView []
  | cs_single : ∀ x : X, ListConsSnocView [x]
  | cs_cc : ∀ (x y : X) {xs : list X},
    ListConsSnocView xs → ListConsSnocView (x :: xs ++ [y])
.
Fixpoint append_snoc
    {X : Type} {xs : list X} (view : ListConsSnocView xs) (x : X) :
    ListConsSnocView (xs ++ [x]) :=
  match view with
  | cs_nil => cs_single x
  | cs_single h => cs_cc h x cs_nil
  | cs_cc h last view' => cs_cc h x (append_snoc view' last)
  end.

Theorem list_cons_snoc_view_tr: ∀ {X : Type}
    (xs : list X) {xsv : list X} (view : ListConsSnocView xsv),
    ListConsSnocView (xsv ++ xs).
Proof.
  induction xs as [| h t IH]; intros.
  - rewrite app_nil_r. assumption.
  - set (view' := append_snoc view h).
    apply IH in view'. rewrite <- app_assoc in view'. simpl in view'.
    assumption.
Qed.

Definition list_cons_snoc_view {X : Type} (xs : list X) : ListConsSnocView xs :=
    list_cons_snoc_view_tr xs cs_nil.

Theorem rev_eq_pal : ∀ {X : Type} {xs : list X},
  xs = rev xs → Palindrome xs.
Proof.
  intros until xs.
  induction (list_cons_snoc_view xs) as [| x | x y xs' cc' IH]; intros.
  - constructor.
  - apply pal_single.
  - simpl in H. rewrite rev_app_distr in H. simpl in H.
    injection H. intros xsy_eq_rxsx xy.
    rewrite xy. rewrite xy in xsy_eq_rxsx.
    apply app_inv_tail in xsy_eq_rxsx.
    apply IH in xsy_eq_rxsx.
    apply pal_cat. assumption.
Qed.

Definition Disjoint {X : Type} (xs ys : list X) : Prop :=
  ∀ x : X, In x xs → ¬ In x ys
.

Inductive NoDup {X : Type}: list X → Prop :=
  | nd_nil : NoDup []
  | nd_cons : ∀ (x : X) (xs : list X), ¬ In x xs → NoDup xs → NoDup (x :: xs)
.

Theorem in_app : ∀ {X : Type} {a : X} (xs ys : list X),
  In a (xs ++ ys) → In a xs ∨ In a ys.
Proof.
  induction xs as [| x xs' IH]; intros.
  - simpl. simpl in H. right. assumption.
  - simpl in H. destruct H as [xa | H].
    + left. simpl. left. assumption.
    + apply IH in H. simpl. rewrite or_assoc. right. assumption.
Qed.

Theorem disjoint_app : ∀ {X : Type} {xs ys : list X},
  NoDup xs → NoDup ys → Disjoint xs ys → NoDup (xs ++ ys).
Proof.
  intros X xs ys nodup_xs. generalize dependent ys.
  induction nodup_xs as [| x xs' n_x_in_xs' nodup_xs' IH]
    ; intros ys nodup_ys disj.
  - simpl. assumption.
  - simpl. apply nd_cons.
    + intros in_xs'_ys. apply in_app in in_xs'_ys as [in_xs' | in_ys].
      contradiction.
      cut (¬ In x ys). intro. contradiction.
      unfold Disjoint. apply disj. simpl. left. reflexivity.
    + apply IH. assumption. unfold Disjoint. unfold Disjoint in disj.
      apply (all_in_in_tail (λ x, ¬ In x ys) disj).
Qed.
