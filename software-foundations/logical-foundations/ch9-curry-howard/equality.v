Require Import Utf8.

Module MyEquality.

Inductive eq {X:Type} : X → X → Prop :=
| eq_refl : ∀x, eq x x.

Notation "x == y" := (eq x y) (at level 70, no associativity) : type_scope.

Lemma equality__leibniz_equality : ∀(X : Type) (x y: X),
  x == y → ∀ P : X → Prop, P x → P y.
Proof.
  intros X x y x_eq_y P.
  Check eq_ind.
  assert (∀ x : X, P x → P x) as H.
  - intros. assumption.
  - set (H' := eq_ind X (fun x y => P x → P y) H x y x_eq_y).
    simpl in H'.
    assumption.
Qed.

Lemma leibniz_equality__equality : ∀ (X : Type) (x y: X),
  (∀ P : X → Prop, P x → P y) → x == y.
  intros.
  apply H.
  apply eq_refl.
Qed.

End MyEquality.
