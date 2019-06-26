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

Definition factorial : com :=
  (* X = m *)
  Y ::= 1 ;;
  (* Y * X! = m! *)
  WHILE ¬ (X = 0) DO
    (* Y * X! = m! ∧ X ≠ 0 *)
    (* Y * X * (X - 1)! = m! *)
    Y ::= Y * X ;;
    (* Y * (X - 1)! = m! *)
    X ::= X - 1
    (* Y * X! = m! *)
  END
  (* Y * X! = m! ∧ ¬ (X ≠ 0) *)
  (* Y = m! *)
.

Lemma negb_sym' : ∀ a b,
  negb a = b → a = negb b.
Proof.
  intros. rewrite <- H.
  now rewrite negb_involutive.
Qed.

Lemma fact_nz : ∀ x,
  x ≠ 0 → fact x = x * fact (x - 1).
Proof.
  induction x.
  - intros. contradiction.
  - intros. simpl. now rewrite sub_0_r.
Qed.

Example factorial_proof : ∀ m,
  {{ fun st => st X = m }}
    factorial
  {{ fun st => st Y = fact m }}.
Proof.
  unfold factorial. intros m.
  apply hoare_seq with
    (fun st => st Y * fact (st X) = fact m).
  (* while *)
  eapply hoare_consequence_post.
  apply hoare_while.

  (* while body *)
  eapply hoare_seq.
  (* X ::= X - 1 *)
  apply hoare_assign.
  (* Y ::= Y * X *)
  eapply hoare_consequence_pre.
  apply hoare_assign.

  (* Y * X! = m! ∧ X ≠ 0 ->> Y * X * (X - 1)! = m! *)
  - unfold assn_sub. unfold t_update. unfold bassn. simpl.
    intros st [Y_X'_m' n_X_0].
    apply negb_sym' in n_X_0.
    apply beq_nat_false in n_X_0.
    rewrite <- mult_assoc.
    now rewrite <- (fact_nz (st X) n_X_0).

  (* Y * X! = m! ∧ ¬ (X ≠ 0) ->> Y! = m! *)
  - unfold bassn. simpl.
    intros st [Y_X'_m' X_0].
    apply not_true_is_false in X_0.
    apply negb_sym' in X_0.
    apply beq_nat_true in X_0.
    rewrite X_0 in Y_X'_m'. simpl in Y_X'_m'.
    now rewrite mult_1_r in Y_X'_m'.

  (* Y ::= 1 *)
  - eapply hoare_consequence_pre.
    apply hoare_assign.
    intros st Xm.
    unfold assn_sub. unfold t_update. simpl.
    rewrite plus_0_r. auto.
Qed.

Lemma min_0 : ∀ x y,
  x = 0 ∨ y = 0 → min x y = 0.
Proof.
  intros. destruct H; rewrite H.
  - apply min_0_l.
  - apply min_0_r.
Qed.

Lemma min_minus_1 : ∀ x y,
  min (x - 1) (y - 1) = min x y - 1.
Proof.
  destruct x; intros.
  - simpl. reflexivity.
  - destruct y; simpl.
    + now rewrite min_0_r.
    + now repeat rewrite sub_0_r.
Qed.

Definition imp_min : com :=
  (* X = a ∧ Y = b *)
  (* 0 + min X Y = min a b *)
  Z ::= 0;;
  (* Z + min X Y = min a b *)
  WHILE (¬ (X = 0)) && (¬ (Y = 0)) DO
    (* Z + min X Y = min a b ∧ (X ≠ 0) && (Y ≠ 0) *)
    (* Z + 1 + min (X - 1) (Y - 1) = min a b *)
    X ::= X - 1;;
    (* Z + 1 + min X (Y - 1) = min a b *)
    Y ::= Y - 1;;
    (* Z + 1 + min X Y = min a b *)
    Z ::= Z + 1
    (* Z + min X Y = min a b *)
  END
  (* Z + min X Y = min a b ∧ ¬ ((X ≠ 0) && (Y ≠ 0))*)
  (* Z = min a b *)
.

Lemma not_0_S : ∀ x,
  x ≠ 0 → ∃ y, x = S y.
Proof.
  intros. destruct x.
  - contradiction.
  - now exists x.
Qed.

Lemma n_beq_nat_false : ∀ x y,
  negb (x =? y) = false → x = y.
Proof.
  intros.
  apply negb_sym' in H.
  now apply beq_nat_true.
Qed.

Example imp_min_proof : ∀ a b,
  {{ fun st => st X = a ∧ st Y = b }}
    imp_min
  {{ fun st => st Z = min a b }}.
Proof.
  unfold imp_min. intros a b.
  apply hoare_seq with
    (fun st => st Z + min (st X) (st Y) = min a b).

  (* WHILE *)
  eapply hoare_consequence_post.
  (* WHILE body *)
  apply hoare_while.
  eapply hoare_seq.
  eapply hoare_seq.
  (* Z ::= Z + 1 *)
  apply hoare_assign.
  (* Y ::= Y - 1 *)
  apply hoare_assign.
  (* X ::= X - 1 *)
  eapply hoare_consequence_pre.
  apply hoare_assign.

  (* Z + min X Y = min a b ∧ (X ≠ 0) && (Y ≠ 0) *)
  (* Z + 1 + min (X - 1) (Y - 1) = min a b *)
  - unfold bassn. unfold assn_sub. unfold t_update. simpl.
    intros st [Z_minXY_minab n_X_0_n_Y_0].
    apply andb_true_iff in n_X_0_n_Y_0 as [n_X_0 n_Y_0].
    apply negb_sym' in n_X_0. apply beq_nat_false in n_X_0.
    apply negb_sym' in n_Y_0. apply beq_nat_false in n_Y_0.
    apply not_0_S in n_X_0 as [x' Ex'].
    apply not_0_S in n_Y_0 as [y' Ey'].
    rewrite Ex', Ey'. rewrite Ex', Ey' in Z_minXY_minab.
    simpl. repeat rewrite sub_0_r.
    simpl in Z_minXY_minab.
    now rewrite <- add_assoc.
  
  (* Z + min X Y = min a b ∧ ¬ ((X ≠ 0) && (Y ≠ 0))*)
  (* Z = min a b *)
  - unfold bassn. simpl.
    intros st [Z_minXY_minab n_X_0_Y_0].
    apply not_true_is_false in n_X_0_Y_0.
    apply andb_false_iff in n_X_0_Y_0 as [H | H];
      apply n_beq_nat_false in H;
      rewrite H in Z_minXY_minab;
      [> rewrite min_0_l in Z_minXY_minab | rewrite min_0_r in Z_minXY_minab];
      now rewrite plus_0_r in Z_minXY_minab.

  (* Z ::= 0 *) 
  - eapply hoare_consequence_pre.
    apply hoare_assign.

    (* X = a ∧ Y = b *)
    (* 0 + min X Y = min a b *)
    intros st [Xa Yb].
    unfold assn_sub. unfold t_update. simpl.
    congruence.
Qed.

(* two loops *)
(*
{{ True }}
{{ 0 = 0 ∧ 0 = 0 ∧ c = 0 }}
X ::= 0 ;;
{{ X = 0 ∧ 0 = 0 ∧ c = 0 }}
Y ::= 0 ;;
{{ X = 0 ∧ Y = 0 ∧ c = 0 }}
Z ::= c ;;
{{ X = 0 ∧ Y = 0 ∧ Z = c }}
{{ Z = X + c ∧ Y = 0 }}
WHILE ¬ (X = a) DO
  {{ Z = X + c ∧ Y = 0 ∧ X ≠ a }}
  {{ Z + 1 = X + 1 + c }}
  X ::= X + 1;;
  {{ Z + 1 = X + c }}
  Z ::= Z + 1
  {{ Z = X + c ∧ Y = 0 }}
END ;;
{{ Z = X + c ∧ Y = 0 ∧ X = a }}
{{ Z = Y + a + c }}
WHILE ¬ (Y = b) DO
  {{ Z = Y + a + c ∧ Y ≠ b }}
  {{ Z + 1 = Y + 1 + a + c }}
  Y ::= Y + 1;;
  {{ Z + 1 = Y + a + c }}
  Z ::= Z + 1
  {{ Z = Y + a + c }}
END
{{ Z = Y + a + c ∧ Y = b }}
{{ Z = a + b + c }}
*)

Lemma pow2_add : ∀ x,
  2 ^ x + 2 ^ x = 2 ^ (x + 1).
Proof.
  induction x.
  - reflexivity.
  - simpl. repeat rewrite add_0_r.
    now rewrite IHx.
Qed.

Example power_series : ∀ m : nat,
  {{ fun st => st X = 0 ∧ st Y = 1 ∧ st Z = 1 }}
    (* Y = 2 ^ (1 + X) - 1 ∧ Z = 2 ^ X *)
    WHILE ¬ (X = m) DO
      (* Y = 2 ^ (1 + X) - 1 ∧ Z = 2 ^ X ∧ X ≠ m *)
      (* Y + 2 * Z = 2 ^ (1 + X + 1) - 1 ∧ 2 * Z = 2 ^ (X + 1)*)
      Z ::= 2 * Z;;
      (* Y + Z = 2 ^ (1 + X + 1) - 1 ∧ Z = 2 ^ (X + 1)*)
      Y ::= Y + Z;;
      (* Y = 2 ^ (1 + X + 1) - 1 ∧ Z = 2 ^ (X + 1)*)
      X ::= X + 1
      (* Y = 2 ^ (1 + X) - 1 ∧ Z = 2 ^ X *)
    END
    (* Y = 2 ^ (1 + X) - 1 ∧ Z = 2 ^ X ∧ X = m *)
  {{ fun st => st Y = 2 ^ (1 + m) - 1 }}.
Proof.
  intros m.
  apply hoare_consequence_pre with
    (fun st => st Y = 2 ^ (1 + st X) - 1 ∧ st Z = 2 ^ st X).

  all: cycle 1. (* solve the trivial one *)
  (* X = 0 ∧ Y = 1 ∧ Z = 1 ->> Y = 2 ^ (1 + X) - 1 ∧ Z = 2 ^ X *)
  intros st [X0 [Y1 Z1]]. rewrite X0, Y1, Z1. easy.

  eapply hoare_consequence_post.
  apply hoare_while.

  all: cycle 1.
  (* Y = 2 ^ (1 + X) - 1 ∧ Z = 2 ^ X ∧ X = m ->> Y = 2 ^ (1 + m) - 1 *)
  unfold bassn. simpl. intros st [[Eyx Ezx] Xm].
  apply not_true_is_false in Xm.
  apply n_beq_nat_false in Xm.
  congruence.

  (* WHILE body *)
  eapply hoare_seq.
  eapply hoare_seq.
  apply hoare_assign.
  apply hoare_assign.
  eapply hoare_consequence_pre.
  apply hoare_assign.
  unfold bassn. unfold assn_sub. unfold t_update. simpl.
  intros st [[YX ZX] _]. rewrite YX, ZX. split.
  - repeat rewrite add_0_r.
    rewrite pow2_add. Omega.omega.
  - rewrite add_0_r.
    apply pow2_add.
Qed.
