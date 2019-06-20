Require Import Equiv.Relation.
Require Import Equiv.Inequivalence.

Theorem swap_noninterfering_assignments_approx : ∀ x y xv yv st st',
  x ≠ y → not_used x yv → not_used y xv →
  st =[ x ::= xv ;; y ::= yv ]=> st' →
  st =[ y ::= yv ;; x ::= xv ]=> st'.
Proof.
  intros until st'. intros NE NUx NUy H.
  inversion H. inversion H2. inversion H5. subst.

  replace (aeval (x !-> aeval st xv; st) yv) with (aeval st yv)
    by (symmetry; apply aeval_weakening; assumption).
  
  replace (y !-> aeval st yv; x !-> aeval st xv; st)
     with (x !-> aeval st xv; y !-> aeval st yv; st)
    by (symmetry; apply t_update_permute; assumption).

  replace (aeval st xv) with (aeval (y !-> aeval st yv; st) xv)
    by (apply aeval_weakening; assumption).

  apply E_Seq with (y !-> aeval st yv; st);
  apply E_Ass; reflexivity.
Qed.

Theorem swap_noninterfering_assignments : ∀ x y xv yv,
  x ≠ y → not_used x yv → not_used y xv →
  cequiv (x ::= xv ;; y ::= yv) (y ::= yv ;; x ::= xv).
Proof.
  intros. split;
  apply swap_noninterfering_assignments_approx;
  try assumption.
  apply not_eq_sym. assumption.
Qed.

