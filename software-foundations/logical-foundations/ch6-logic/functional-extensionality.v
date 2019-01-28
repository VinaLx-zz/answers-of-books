Require Import List.
Import ListNotations.

Require Import FunctionalExtensionality.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Theorem rev_append_rev : forall {X : Type} (xs ys : list X),
  rev_append xs ys = rev xs ++ ys.
Proof.
  intros until xs.
  induction xs as [| h t IH]; intros.
  - reflexivity.
  - simpl. rewrite <- app_assoc.
    simpl. apply IH.              
Qed.

Theorem tr_rev_correct' : forall (X : Type) (xs : list X),
  @tr_rev X xs = @rev X xs.
Proof.
  intros. unfold tr_rev.
  destruct xs.
  - reflexivity.
  - simpl. apply rev_append_rev.
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intro X.
  apply functional_extensionality.
  apply tr_rev_correct'.
Qed.

