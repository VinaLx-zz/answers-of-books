Require Import Utf8.
Require Import String.
Require Import Bool.
Require Import FunctionalExtensionality.

Definition total_map (A : Type) := string → A.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : ∀s : string, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem eqb_string_true_iff : ∀x y : string,
    eqb_string x y = true ↔ x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.

Theorem eqb_string_false_iff : ∀x y : string,
    eqb_string x y = false ↔ x ≠ y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity.
Qed.

Theorem false_eqb_string : ∀x y : string,
   x ≠ y → eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

Definition t_empty {A : Type} (v : A) : total_map A := (λ _, v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v) (at level 100, right associativity).

Notation "x '!->' v ';' m" :=
    (t_update m x v) (at level 100, v at next level, right associativity).

Lemma t_apply_empty : ∀(A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  intros.
  reflexivity.
Qed.

Lemma t_update_eq : ∀(A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update. rewrite <- eqb_string_refl.
  reflexivity.
Qed.

Theorem t_update_neq : ∀(A : Type) (m : total_map A) x1 x2 v,
  x1 ≠ x2 → (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update.
  apply eqb_string_false_iff in H. rewrite H.
  reflexivity.
Qed.

Lemma t_update_shadow : ∀(A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. unfold t_update.
  apply functional_extensionality. intros s.
  destruct (eqb_string x s); reflexivity.
Qed.

Lemma eqb_stringP : ∀ x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros.
  destruct (eqb_string x y) eqn: E.
  - apply ReflectT. apply eqb_string_true_iff. assumption.
  - apply ReflectF. apply eqb_string_false_iff. assumption.
Qed.

Theorem t_update_same : ∀(A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  intros. unfold t_update.
  apply functional_extensionality. intros s.
  destruct (eqb_string x s) eqn: E.
  - apply eqb_string_true_iff in E. rewrite E. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : ∀(A : Type) (m : total_map A) v1 v2 x1 x2,
    x2 ≠ x1 → (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  apply functional_extensionality. intro.
  unfold t_update.
  destruct (eqb_string x1 x) eqn: E1; destruct (eqb_string x2 x) eqn: E2.
  - apply eqb_string_true_iff in E1. apply eqb_string_true_iff in E2.
    rewrite <- E1 in E2. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

