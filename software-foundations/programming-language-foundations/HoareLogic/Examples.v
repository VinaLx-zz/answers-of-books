Require Import HoareLogic.ProofRules.
Require Import LF.Imp.
Require Import Utf8.
Require Omega.
Require Import Arith. Import Nat.
Require Import Bool.

Definition ex1_src : com :=
  (* True *)
  TEST X ≤ Y THEN
    (* True ∧ X ≤ Y *)
    (* Y = X + (Y - X) *)
    Z ::= Y - X
    (* Y = X + Z *)
  ELSE
    (* True ∧ ¬ X ≤ Y *)
    (* X + Z = X + Z *)
    Y ::= X + Z
    (* Y = X + Z *)
  FI
  (* Y = X + Z *)
.

Example ex1 : {{ fun st => True }} ex1_src {{ fun st => st Y = st X + st Z }}.
Proof.
  unfold ex1_src.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    apply hoare_assign.
    unfold bassn. unfold assn_sub. unfold t_update. simpl.
    intros st [_ x_le_y].
    apply leb_le in x_le_y.
    Omega.omega.
  - eapply hoare_consequence_pre.
    apply hoare_assign.
    unfold bassn. unfold assn_sub. unfold t_update. simpl.
    intros st [_ n_x_le_y].
    reflexivity.
Qed.

Definition slow_assignment : com :=
  (* X = m *)
  Y ::= 0;;
  (* Y = 0 ∧ X = m *)
  (* X + Y = m *)
  WHILE ¬ (X = 0) DO
    (* X + Y = m *)
    (* (X - 1) + (Y + 1) = m *)
    X ::= X - 1;;
    (* X + (Y + 1) = m *)
    Y ::= Y + 1
    (* X + Y = m *)
  END
  (* X + Y = m ∧ ¬ (¬ (X = 0)) *)
  (* Y = m *)
.

Example slow_assignment_proof : ∀ m,
  {{ fun st => st X = m }}
    slow_assignment
  {{ fun st => st Y = m }}.
Proof.
  unfold slow_assignment.
  intros m.
  eapply hoare_consequence_post with
    (fun st => (fun st => st X + st Y = m) st ∧ ¬ (bassn (¬ (X = 0)) st) ).
  eapply hoare_seq.
  all: cycle 1.
  eapply hoare_consequence_pre.
  eapply hoare_assign.
  all: cycle 2.
  apply hoare_while.
  eapply hoare_seq.
  apply hoare_assign.
  eapply hoare_consequence_pre.
  apply hoare_assign.
  all: (unfold bassn; simpl).
  - intros st [ X_Y_m n_X_0 ].
    assert (st X ≠ 0) as X_ne_0. {
      symmetry in n_X_0.
      apply negb_sym in n_X_0. simpl in n_X_0.
      now apply beq_nat_false.
    } 
    unfold assn_sub. unfold t_update. simpl.
    Omega.omega.
  - unfold assn_sub. unfold t_update. simpl.
    intros st H. now rewrite add_0_r.
  - intros st. simpl. intros [ X_Y_m X_0 ].
    apply not_true_is_false in X_0.
    symmetry in X_0.
    apply negb_sym in X_0. simpl in X_0.
    apply beq_nat_true in X_0.
    now rewrite X_0 in X_Y_m.
Qed.

Definition slow_add : com :=
  (* X = m ∧ Z = n *)
  (* X + Z = n + m *)
  WHILE ¬(X = 0) DO
    (* X + Z = n + m ∧ ¬ X = 0 *)
    (* X - 1 + (Z + 1) = m + n *)
    Z ::= Z + 1;;
    (* X - 1 + Z = m + n *)
    X ::= X - 1
    (* X + Z = m + n *)
  END
  (* X + Z = m + n ∧ X = 0 *)
  (* Z = m + n *)
.

Example slow_add_proof : ∀ m n,
  {{ fun st => st X = m ∧ st Z = n }}
    slow_add
  {{ fun st => st Z = m + n }}.
Proof.
  intros m n. unfold slow_add.
  eapply hoare_consequence_pre.
  apply hoare_consequence_post with
    (fun st => (fun st => st X + st Z = m + n) st ∧ ¬ (bassn (¬ (X = 0)) st)).
  apply hoare_while.
  eapply hoare_seq.
  apply hoare_assign.
  eapply hoare_consequence_pre.
  apply hoare_assign.
  all: unfold bassn.
  - unfold assn_sub. unfold t_update. simpl.
    intros st [XZ_mn n_X_0]. symmetry in n_X_0.
    apply negb_sym in n_X_0.
    apply beq_nat_false in n_X_0.
    Omega.omega.
  - simpl. intros st [XZ_mn nn_X_0].
    apply not_true_is_false in nn_X_0.
    symmetry in nn_X_0. apply negb_sym in nn_X_0.
    apply beq_nat_true in nn_X_0.
    Omega.omega.
  - intros st [Xm Zn]. auto.
Qed.

Fixpoint parity x :=
  match x with
  | 0 => 0
  | 1 => 1
  | S (S x') => parity x'
  end
.

Lemma parity_ge_2 : ∀ x,
  2 ≤ x → parity (x - 2) = parity x.
Proof.
  induction x; intros.
  - reflexivity.
  - destruct x.
    + inversion H. inversion H1.
    + simpl. now rewrite <- minus_n_O.
Qed.

Lemma parity_lt_2 : ∀ x,
  ¬ 2 ≤ x → parity x = x.
Proof.
  destruct x as [| x']; intros.
  - reflexivity.
  - intros. destruct x' as [| x''].
    + reflexivity.
    + assert (2 ≤ S (S x'')).
      repeat apply le_n_S.
      apply le_0_n.
      contradiction.
Qed.

Lemma nleb_nle : ∀ m n, m <=? n = false → ¬ m ≤ n.
Proof.
  induction m; intros.
  - destruct n; inversion H.
  - destruct n.
    + intros Sm_le_0. inversion Sm_le_0.
    + simpl in H. apply IHm in H.
      intros Sm_le_Sn. apply le_S_n in Sm_le_Sn.
      contradiction.
Qed.

Theorem parity_correct : ∀ m,
  {{ fun st => st X = m }}
    WHILE 2 ≤ X DO
      X ::= X - 2
    END
  {{ fun st => st X = parity m }}.
Proof.
  intros m.
  apply hoare_consequence_pre with
    (fun st => parity (st X) = parity m).
  eapply hoare_consequence_post.
  apply hoare_while; unfold bassn.
  - eapply hoare_consequence_pre.
    eapply hoare_assign.
    intros st [pX_pm x_ge_2].
    unfold assn_sub. unfold t_update. simpl.
    unfold beval in x_ge_2. apply leb_le in x_ge_2. simpl in x_ge_2.
    rewrite <- pX_pm.
    now apply parity_ge_2.
  - unfold bassn. unfold beval. intros st [pX_pm n_2_le_X]. 
    apply not_true_is_false in n_2_le_X.
    apply nleb_nle in n_2_le_X. simpl in n_2_le_X.
    rewrite <- pX_pm. symmetry.
    now apply parity_lt_2.
  - intros st H. auto.
Qed.
