Require Import HoareLogic.ProofRules.
Require Import LF.Imp.
Require Import Utf8.
Require Omega.

Definition is_wp (P : Assertion) (c : com) (Q : Assertion) :=
  {{ P }} c {{ Q }} ∧ ∀ P', {{ P' }} c {{ Q }} → (P' ->> P).

Theorem is_wp_example :
  is_wp (fun st => st Y ≤ 4) (X ::= Y + 1) (fun st => st X ≤ 5).
Proof.
  unfold is_wp. split.
  - eapply hoare_consequence_pre.
    apply hoare_assign.
    unfold assn_sub. unfold t_update. simpl.
    intros st H.
    Omega.omega.
  - intros P' Ht st P'st.
    unfold hoare_triple in Ht.
    remember (X !-> aeval st (Y + 1); st) as st'.
    assert (st =[ X ::= Y + 1 ]=> st') as H by (rewrite Heqst'; now apply E_Ass).
    apply Ht in H. 2: assumption.
    unfold t_update in st'. 
    rewrite Heqst' in H. unfold t_update in H. simpl in H.
    Omega.omega.
Qed.
