Require Import PeanoNat.
Import Nat.
Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Omega.

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T → reg_exp → Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Lemma empty_is_empty : ∀ T (s : list T),
  ¬(s =~ EmptySet).
Proof.
  intros T s s_m_empty.
  inversion s_m_empty.
Qed.

Lemma MUnion' : ∀ T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 ∨ s =~ re2 → s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [s_m_re1 | s_m_re2].
  - apply MUnionL. assumption.
  - apply MUnionR. assumption.
Qed.

Theorem in_reduce : ∀ (T : Type) (P : T → Prop) (x : T) (xs : list T),
  (∀ y: T, In y (x :: xs) → P y) → (∀ y' : T, In y' xs → P y').
Proof.
  intros T P x xs py_xxs y' py'_xs.
  apply py_xxs. simpl. right. assumption.
Qed.

Lemma MStar' : ∀ T (ss : list (list T)) (re : reg_exp),
  (∀s, In s ss → s =~ re) →
  fold_right (@app T) [] ss =~ Star re.
Proof.
  intros T ss re all_s_m_re.
  induction ss as [| s ss' IH].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply all_s_m_re. simpl. left. reflexivity.
    + set (all_s'_m_re := in_reduce (list T) (λ s, s =~ re) s ss' all_s_m_re).
      apply IH. apply all_s'_m_re.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Theorem list_regex_sound : ∀ (T : Type) (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 → s1 = s2.
Proof.
  intros until s2. generalize dependent s1.
  induction s2 as [| h2 t2 IH]; intros.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H.
    inversion H3. simpl.
    apply IH in H4. rewrite H4.
    reflexivity.
Qed.

Theorem list_regex_complete : ∀ (T : Type) (s1 s2 : list T),
  s1 = s2 → s1 =~ reg_exp_of_list s2.
Proof.
  intros until s2. generalize dependent s1.
  induction s2 as [| h2 t2 IH]; intros.
  - rewrite H. simpl. apply MEmpty.
  - rewrite H. simpl.
    assert (h2 :: t2 = [h2] ++ t2) as cons_app by reflexivity.
    rewrite cons_app.
    apply MApp.
    + apply MChar.
    + apply IH. reflexivity.
Qed.

Lemma reg_exp_of_list_spec : ∀ (T : Type) (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 ↔ s1 = s2.
Proof.
  intros. split.
  - apply list_regex_sound.
  - apply list_regex_complete.
Qed.

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App x y => re_not_empty x && re_not_empty y
  | Union x y => re_not_empty x || re_not_empty y
  | Star re => true
  end.

Theorem re_not_empty_sound : ∀ T (re : @reg_exp T),
  re_not_empty re = true → (∃ s, s =~ re).
Proof.
  intros. induction re; simpl in H.
  - discriminate H.
  - exists []. apply MEmpty.
  - exists [t0]. apply MChar.
  - apply andb_true_iff in H as [re1_ne re2_ne].
    apply IHre1 in re1_ne as [s1 s1_m_re1].
    apply IHre2 in re2_ne as [s2 s2_m_re2].
    exists (s1 ++ s2). apply MApp; assumption.
  - apply orb_true_iff in H as [re1_ne | re2_ne].
    + apply IHre1 in re1_ne as [s1 s1_m_re1].
      exists s1. apply MUnionL. assumption.
    + apply IHre2 in re2_ne as [s2 s2_m_re2].
      exists s2. apply MUnionR. assumption.
  - exists []. apply MStar0.
Qed.

Theorem re_not_empty_complete : ∀ T (re : @reg_exp T),
  (∃ s, s =~ re) → re_not_empty re = true.
Proof.
  intros T re [s s_m_re].
  induction s_m_re; try reflexivity; simpl.
  - rewrite IHs_m_re1. rewrite IHs_m_re2. reflexivity.
  - rewrite IHs_m_re. reflexivity.
  - rewrite IHs_m_re. destruct (re_not_empty re1); reflexivity.
Qed.

Lemma re_not_empty_correct : ∀ T (re : @reg_exp T),
  (∃s, s =~ re) ↔ re_not_empty re = true.
Proof.
  intros. split;
  solve [apply re_not_empty_sound | apply re_not_empty_complete].
Qed.

Lemma MStar'' : ∀ T (s : list T) (re : reg_exp),
  s =~ Star re →
  ∃ss : list (list T),
    s = fold_right (@app T) [] ss ∧ ∀ s', In s' ss → s' =~ re.
Proof.
  intros T s re s_m_star_re.
  remember (Star re) as star_re eqn: EStarRe.
  induction s_m_star_re; try discriminate.
  - exists []. split. reflexivity. intros. contradiction.
  - set (H := IHs_m_star_re2 EStarRe).
    destruct H as [ss2 [E_s2_fold_ss2 all_s2_m_re]].
    exists (s1 :: ss2). split.
    + simpl. rewrite <- E_s2_fold_ss2. reflexivity. 
    + simpl. intros s' [E_s'_s1 | s'_in_ss2].
      * rewrite <- E_s'_s1. injection EStarRe.
        intros H'. rewrite <- H'. assumption.
      * apply all_s2_m_re. assumption.
Qed.

Module Pumping.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.
Lemma napp_plus: ∀T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Theorem le_loose : ∀ m n, S m ≤ n → m ≤ n.
Proof.
  intros m n sm_le_n.
  induction sm_le_n as [| pn sm_le_pn IH].
  - apply le_S. apply le_n.
  - apply le_S. apply IH.
Qed.

Theorem plus_le_l : ∀ n m o : nat,
  n + m ≤ o → n ≤ o.
Proof.
  induction m as [| m' IH].
  - rewrite <- plus_n_O. intros. assumption.
  - rewrite <- plus_n_Sm. intros o s_nm_le_o.
    apply le_loose in s_nm_le_o.
    apply IH. assumption.
Qed.

Theorem plus_le_r : ∀ n m o : nat,
  n + m ≤ o → m ≤ o.
Proof.
  intros. rewrite add_comm in H. apply plus_le_l with n. assumption.
Qed.

Theorem plus_le_plus : ∀ a b c d : nat,
  a + b ≤ c + d → a ≤ c ∨ b ≤ d.
Proof.
  induction a as [| a' IH]; intros.
  - left. apply le_O_n.
  - destruct c as [| c'].
    + rewrite plus_O_n in H.
      right. apply plus_le_r with (S a'). apply H.
    + simpl in H. apply le_S_n in H. apply IH in H.
      destruct H as [a'_le_c' | b_le_d].
      left. apply le_n_S. assumption.
      right. assumption.
Qed.

Theorem star_match_napp : ∀ T (re : @reg_exp T) (s : list T) (n : nat),
  s =~ re → napp n s =~ Star re.
Proof.
  intros.
  induction n as [| n' IH]; simpl.
  - apply MStar0.
  - apply MStarApp. apply H. apply IH.
Qed.

Lemma pumping : ∀ T (re : @reg_exp T) s,
  s =~ re → pumping_constant re ≤ length s →
  ∃s1 s2 s3,
    s = s1 ++ s2 ++ s3 ∧
    s2 ≠ [] ∧
    ∀m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ]
    ; simpl.
  - omega.
  - omega.
  - (* MApp *)
    rewrite app_length. intro pump_premise.
    apply plus_le_plus in pump_premise as [re1_le_l1 | re2_le_l2].
    + apply IH1 in re1_le_l1 as [s12 [s13 [s14 [E_s1_s234 [n_s13_nil pump]]]]].
      exists s12. exists s13. exists (s14 ++ s2).
      split; try split.
      (* s1 ++ s2 = s12 ++ s13 ++ s14 ++ s2 *)
        rewrite E_s1_s234. repeat rewrite <- app_assoc.
        reflexivity.
      (* s13 ≠ [] *)
        apply n_s13_nil.
      (* ∀ m : nat, s12 ++ napp m s13 ++ s14 ++ s2 =~ App re1 re2 *)
        intro m.
        rewrite app_assoc. rewrite app_assoc.
        rewrite <- (app_assoc s12 (napp m s13) s14).
        apply MApp. apply pump. apply Hmatch2.
    + apply IH2 in re2_le_l2 as [s22 [s23 [s24 [E_s2_s234 [n_s23_nil pump]]]]].
      exists (s1 ++ s22). exists s23. exists s24.
      split; try split.
      (* s1 ++ s2 = (s1 ++ s22) ++ s23 ++ s24 *)
      rewrite E_s2_s234. repeat rewrite app_assoc.
      reflexivity.
      (* s23 ≠ [] *)
      apply n_s23_nil.
      (* ∀ m : nat, (s1 ++ s22) ++ napp m s23 ++ s24 =~ App re1 re2 *)
      intro m.
      rewrite <- app_assoc.
      apply MApp. apply Hmatch1. apply pump.
  - (* MUnionL *)
    intro H. apply plus_le_l in H.
    apply IH in H as [s2 [s3 [s4 [E_s1_s234 [n_n3_nil pump]]]]].
    exists s2. exists s3. exists s4. split; try split; try assumption.
    intros m. apply MUnionL. apply pump.
  - (* MUnionR *)
    intro H. apply plus_le_r in H.
    apply IH in H as [s3 [s4 [s5 [E_s2_s345 [n_n4_nil pump]]]]].
    exists s3. exists s4. exists s5. split; try split; try assumption.
    intros m. apply MUnionR. apply pump.
  - omega.
  - (* MStarApp *)
    destruct s2 eqn: E2.
    + (* length s2 = 0 *)
      destruct s1 eqn: E1.
      (* length s1 = 0 && length s2 = 0 *)
      simpl. omega.
      (* 1 ≤ length s1 *)
      intros. exists []. exists s1. exists [].
      rewrite <- E1. simpl. split. reflexivity. split. 
        (* s1 ≠ [] *)
        intro contra. rewrite E1 in contra.
        discriminate contra.
        (* ∀ m : nat, napp m s1 ++ [] =~ Star re *)
        intro m. rewrite app_nil_r.
        apply star_match_napp. rewrite E1. apply Hmatch1.
    + (* 1 ≤ length s2 *)
      simpl in IH2.
      assert (1 ≤ S (length l)) as IH2P by omega.
      apply IH2 in IH2P as [s21 [s22 [s23 [E_s2_s123 [n_s22_nil pump]]]]].
      rewrite <- E2. rewrite <- E2 in E_s2_s123. (* un-destruct s2 *)
      intros. exists (s1 ++ s21). exists s22. exists s23.
      split; try split. simpl.
        (* s1 ++ s2 = (s1 ++ s21) ++ s22 ++ s23 *)
        rewrite <- app_assoc. rewrite E_s2_s123. reflexivity.
        (* s22 ≠ [] *)
        apply n_s22_nil.
        (* ∀ m : nat, (s1 ++ s21) ++ napp m s22 ++ s23 =~ Star re *)
        intro m. rewrite <- app_assoc.
        apply MStarApp. apply Hmatch1. apply pump.
Qed.

End Pumping.

