Require Export OperationalSemantics.tm.
Require Import Relations.

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Ltac solve_by_inverts n :=
  match goal with
  | H : ?T |- _ =>
      match type of T with Prop =>
        solve [
          inversion H;
          match n with S (S (?n')) =>
            subst; solve_by_inverts (S n')
          end
        ]
      end
  end
.

Ltac solve_by_invert := solve_by_inverts 1.

Theorem step_deterministic : deterministic step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
  inversion Hy2; subst; try solve_by_invert.
  - reflexivity.
  - apply IHHy1 in H2. now rewrite H2.
  - apply IHHy1 in H2. now rewrite H2.
Qed.
