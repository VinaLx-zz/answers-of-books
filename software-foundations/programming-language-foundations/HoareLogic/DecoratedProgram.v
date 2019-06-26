Require Import HoareLogic.ProofRules.
Require Import Utf8.
Require Import LF.Imp.

Inductive dcom : Type :=
| DCSkip : Assertion → dcom
| DCSeq : dcom → dcom → dcom
| DCAsgn : string → aexp → Assertion → dcom
| DCIf : bexp → Assertion → dcom → Assertion → dcom → Assertion → dcom
| DCWhile : bexp → Assertion → dcom → Assertion → dcom
| DCPre : Assertion → dcom → dcom
| DCPost : dcom → Assertion → dcom.

Inductive decorated : Type :=
| Decorated : Assertion → dcom → decorated.

Delimit Scope default with default.
Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'TEST' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI' {{ Q }}"
      := (DCIf b P d P' d' Q)
      (at level 80, right associativity) : dcom_scope.
Notation "'->>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity) : dcom_scope.
Notation "d '->>' {{ P }}"
      := (DCPost d P)
      (at level 80, right associativity) : dcom_scope.
Notation " d ;; d' "
      := (DCSeq d d')
      (at level 80, right associativity) : dcom_scope.
Notation "{{ P }} d"
      := (Decorated P d)
      (at level 90) : dcom_scope.
Delimit Scope dcom_scope with dcom.

Bind Scope dcom_scope with dcom.

Fixpoint extract (d : dcom) : com :=
  match d with
  | DCSkip _ => SKIP
  | DCSeq a b => (extract a) ;; (extract b)
  | DCAsgn X a _ => X ::= a
  | DCIf b _ t _ f _ => TEST b THEN extract t ELSE extract f FI
  | DCWhile b _ d _ => WHILE b DO extract d END
  | DCPre _ d => extract d
  | DCPost d _ => extract d
  end
.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated P d => extract d
  end
.

Fixpoint post (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCSeq a b => post b
  | DCAsgn X a P => P
  | DCIf _ _ _ _ _ P => P
  | DCWhile _ _ _ P => P
  | DCPre _ d => post d
  | DCPost c P => P
  end
.

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => P
  end
.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d => post d
  end
.

Definition dec_correct (dec : decorated) :=
  {{ pre_dec dec }} extract_dec dec {{ post_dec dec }}.

Fixpoint verification_conditions (P : Assertion) (d : dcom) : Prop :=
  match d with
  | DCSkip Q => P ->> Q
  | DCSeq a b
      => verification_conditions P a
       ∧ verification_conditions (post a) b
  | DCAsgn X a Q => (P ->> Q [X |-> a])
  | DCIf b Pt t Pf f Q
      => ((fun st => P st ∧   bassn b st) ->> Pt)
       ∧ ((fun st => P st ∧ ¬ bassn b st) ->> Pf)
       ∧ (post t ->> Q) ∧ (post f ->> Q)
       ∧ verification_conditions Pt t
       ∧ verification_conditions Pf f
  | DCWhile b Pbody body Q
      => (P ->> post body)
       ∧ ((fun st => post body st ∧   bassn b st) ->> Pbody)
       ∧ ((fun st => post body st ∧ ¬ bassn b st) ->> Q)
       ∧ verification_conditions Pbody body
  | DCPre P' d
      => (P ->> P')
       ∧ verification_conditions P' d
  | DCPost d Q
      => verification_conditions P d
       ∧ (post d ->> Q)
  end
.

Definition verification_conditions_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d => verification_conditions P d
  end
.

Definition verification_correct : ∀ d P,
  verification_conditions P d → {{ P }} (extract d) {{ post d }}.
Proof.
  induction d; simpl; intros P H.
  - eapply hoare_consequence_pre.
    apply hoare_skip. trivial.
  - destruct H as [Pd1 pd1d2].
    eapply hoare_seq; eauto.
  - eapply hoare_consequence_pre.
    apply hoare_assign. trivial.
  - destruct H as [pre_t [pre_f [post_t [post_f [body_t body_f]]]]].
    eapply hoare_if.
    + eapply hoare_consequence_post.
      eapply hoare_consequence_pre.
      apply IHd1. eassumption. eassumption. eassumption.
    + eapply hoare_consequence_post.
      eapply hoare_consequence_pre.
      apply IHd2. eassumption. eassumption. eassumption.
  - destruct H as [Ppost [body_a [body_post ad]]].
    eapply hoare_consequence_pre.
    eapply hoare_consequence_post.
    apply hoare_while.
    eapply hoare_consequence_pre.
    apply IHd. eassumption.
    all: assumption.
  - destruct H as [Pa ad].
    eapply hoare_consequence_pre; eauto.
  - destruct H as [Pd pda].
    eapply hoare_consequence_post; eauto.
Qed.

