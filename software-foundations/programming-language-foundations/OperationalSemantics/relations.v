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
  intros x y1 y2 Hy1.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    + reflexivity.
    + inversion H2.
    + inversion H3.
  - inversion Hy2; subst. 
    + inversion Hy1.
    + apply IHHy1 in H2. now rewrite H2.
    + inversion H1. subst. inversion Hy1.
  - inversion Hy2; subst.
    + inversion Hy1.
    + inversion H. subst. inversion H3.
    + apply IHHy1 in H4. now rewrite H4.
Qed.

Theorem strong_progress :
  ∀ t, value t ∨ (∃ t', t --> t').
Proof.
  induction t.
  - left. constructor.
  - right. destruct IHt1.
    + destruct IHt2.
      ++ inversion H. inversion H0.
         exists (C (n + n0)).
         constructor.
      ++ destruct H0 as [t' H0].
         exists (P t1 t').
         now apply ST_Plus2.
    + destruct H as [t' H].
      exists (P t' t2).
      now apply ST_Plus1.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.
