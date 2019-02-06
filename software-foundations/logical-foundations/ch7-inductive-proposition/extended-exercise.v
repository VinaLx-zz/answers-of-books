Require Import Utf8.
Require Import List.
Import ListNotations.
Require Import Bool.
Require Import Ascii.

Require Import regex.

Definition string := list ascii.

Lemma app_exists : ∀(s : string) re0 re1,
    s =~ App re0 re1 ↔
    ∃s0 s1, s = s0 ++ s1 ∧ s0 =~ re0 ∧ s1 =~ re1.
Proof.
  intros. split.
  - intros. inversion H. exists s1, s2. split.
    + reflexivity.
    + split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

Lemma app_ne : ∀ (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) ↔
  ([] =~ re0 ∧ a :: s =~ re1) ∨
  ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re0 ∧ s1 =~ re1.
Proof.
  intros. split; intros.
  - apply app_exists in H as [s0 [s1 [as_s01 [s0_m_re0 s1_m_re1]]]].
    destruct s0; simpl in as_s01.
    + left. split. assumption. rewrite as_s01. assumption. 
    + inversion as_s01. right. exists s0. exists s1. split.
      reflexivity. split; assumption.
  - destruct H as [ [nil_m_re0 as_m_re1]
                  | [s0 [s1 [s_s01 [as0_m_re0 s1_m_re1]]]]].
    + rewrite <- (app_nil_l (a :: s)). apply MApp; assumption.
    + rewrite s_s01.
      assert (a :: s0 ++ s1 = (a :: s0) ++ s1) as E by reflexivity.
      rewrite E. apply MApp; assumption.
Qed.

Lemma star_ne : ∀ (a : ascii) s re,
  a :: s =~ Star re ↔
  ∃ s0 s1, s = s0 ++ s1 ∧ a :: s0 =~ re ∧ s1 =~ Star re.
Proof.
  intros. split; intros.
  - remember (a :: s) as s'. remember (Star re) as re'.
    induction H; try discriminate Heqs'; try discriminate Heqre'.
    destruct s1 as [| h1 t1]; simpl in Heqs'.
    + apply IHexp_match2; assumption.
    + inversion Heqs'. rewrite H2 in H. exists t1. exists s2.
      split. reflexivity. split.
      inversion Heqre'. rewrite H4 in H. assumption.
      assumption.
  - destruct H as [s0 [s1 [s_s01 [as0_m_re s1_m_star]]]].
    rewrite s_s01.
    assert (a :: s0 ++ s1 = (a :: s0) ++ s1) as E by reflexivity. rewrite E.
    apply MStarApp; assumption.
Qed.

Fixpoint match_eps (re: @reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App r1 r2 => match_eps r1 && match_eps r2
  | Union r1 r2 => match_eps r1 || match_eps r2
  | Star r => true
  end.

Definition refl_matches_eps m :=
  ∀ re : @reg_exp ascii, reflect ([] =~ re) (m re).

Theorem app_nils : ∀ t (xs ys : list t), xs ++ ys = [] → xs = [] ∧ ys = [].
Proof.
  intros. destruct xs; destruct ys. split; reflexivity.
  all: simpl in H; discriminate H. 
Qed.

Lemma match_eps_refl :
  ∀ re : @reg_exp ascii, reflect ([] =~ re) (match_eps re).
Proof.
  unfold refl_matches_eps. intros re.
  induction re.
  - apply ReflectF. intro. inversion H.
  - apply ReflectT. constructor.
  - apply ReflectF. intro. inversion H.
  - simpl. destruct IHre1; destruct IHre2; simpl.
    apply ReflectT. rewrite <- (app_nil_l []). apply MApp; assumption.
    all: apply ReflectF; intro;
    inversion H; apply app_nils in H1; destruct H1 as [s1_nil s2_nil];
      rewrite s1_nil in H3; rewrite s2_nil in H4; contradiction.
  - simpl. destruct IHre1; destruct IHre2; simpl.
    + apply ReflectT. apply MUnionL. assumption.
    + apply ReflectT. apply MUnionL. assumption.
    + apply ReflectT. apply MUnionR. assumption.
    + apply ReflectF. intro. inversion H; contradiction.
  - simpl. apply ReflectT. apply MStar0.
Qed.

Definition is_der re (a : ascii) re' :=
  ∀ s, a :: s =~ re ↔ s =~ re'.

Definition derives d := ∀ a re, is_der re a (d a re).

Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char c => if ascii_dec c a then EmptyStr else EmptySet
  | App r1 r2 => if match_eps r1
      then Union (App (derive a r1) r2) (derive a r2)
      else App (derive a r1) r2
  | Union r1 r2 => Union (derive a r1) (derive a r2)
  | Star re => App (derive a re) (Star re)
  end
.

Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. reflexivity. Qed.

Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. reflexivity. Qed.

Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. reflexivity. Qed.

Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. reflexivity. Qed.

Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. reflexivity. Qed.

Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. reflexivity. Qed.

Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. reflexivity. Qed.

Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. reflexivity. Qed.

Theorem match_derive : ∀ {a : ascii} {re : @reg_exp ascii} {s : string},
  a :: s =~ re → s =~ derive a re.
Proof.
  intros until re. induction re; intros s as_m_re.
  - inversion as_m_re.
  - inversion as_m_re.
  - simpl. destruct (ascii_dec t a).
    + inversion as_m_re. constructor.
    + inversion as_m_re. symmetry in H. contradiction.
  - simpl. inversion as_m_re. destruct (match_eps re1) eqn: E.
    + destruct s1 as [| h1 t1]; simpl in H0.
      { apply MUnionR. apply IHre2. rewrite H0 in H3. assumption. }
      { apply MUnionL. inversion H0. apply MApp.
        { apply IHre1. rewrite <- H5. assumption. }
        { assumption. }
      }
    + destruct s1 as [| h1 t1]; simpl in H0.
      { destruct (match_eps_refl re1).
        discriminate E. contradiction.
      }
      { inversion H0. apply MApp.
        { apply IHre1. rewrite <- H5. assumption. }
        { assumption. }
      }
  - simpl. inversion as_m_re.
    + apply MUnionL. apply IHre1. assumption.
    + apply MUnionR. apply IHre2. assumption.
  - simpl. remember (a :: s) as sa. remember (Star re) as re'.
    induction as_m_re; try discriminate Heqsa; try discriminate Heqre'.
    destruct s1 as [| h1 t1]; simpl in Heqsa.
    + apply IHas_m_re2; assumption.
    + inversion Heqsa. apply MApp.
      { apply IHre.
        rewrite <- H0. inversion Heqre'. rewrite <- H2. assumption. }
      { assumption. }
Qed.

Theorem derive_match : ∀ {a : ascii} {re : @reg_exp ascii} {s : string},
  s =~ derive a re → a :: s =~ re.
Proof.
  intros until re. induction re; simpl; intros.
  - inversion H.
  - inversion H.
  - destruct (ascii_dec t a); inversion H.
    rewrite <- e. constructor.
  - destruct (match_eps re1) eqn: E.
    + inversion H.
      { clear H0. clear H1. clear H3. clear re0. clear re3.
        inversion H2.
        assert (a :: s0 ++ s2 = (a :: s0) ++ s2) as E2 by reflexivity.
        rewrite E2.
        apply MApp. apply IHre1. apply H4. apply H5.
      }
      { rewrite <- (app_nil_l (a :: s)). apply MApp.
        { destruct (match_eps_refl re1). assumption. discriminate E. }
        { apply IHre2. assumption. }
      }
    + inversion H.
      assert (a :: s1 ++ s2 = (a :: s1) ++ s2) as E2 by reflexivity. rewrite E2.
      apply MApp.
      { apply IHre1. assumption. }
      { assumption. }
  - inversion H.
    + apply MUnionL. apply IHre1. assumption.
    + apply MUnionR. apply IHre2. assumption.
  - inversion H.
    assert (a :: s1 ++ s2 = (a :: s1) ++ s2) as E by reflexivity.
    rewrite E. apply MStarApp. apply IHre. assumption. assumption.
Qed.

Lemma derive_corr : ∀ {a : ascii} {re : @reg_exp ascii} {s : string},
  a :: s =~ re ↔ s =~ derive a re.
Proof.
  unfold derives. unfold is_der.
  intros. split.
  - apply match_derive.
  - apply derive_match.
Qed.

Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | h :: t => regex_match t (derive h re)
  end.

Theorem regex_refl : ∀ (s : string) (re : @reg_exp ascii),
  reflect (s =~ re) (regex_match s re).
Proof.
  induction s as [| h t IH]; simpl; intros.
  - apply match_eps_refl.
  - set (ih := IH (derive h re)).
    destruct ih as [refl_t | refl_f].
    + apply ReflectT. apply derive_corr. assumption.
    + apply ReflectF.
      intro H. apply derive_corr in H.
      contradiction.
Qed.

