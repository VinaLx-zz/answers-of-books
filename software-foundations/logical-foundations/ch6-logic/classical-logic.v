Require Import Logic.
Theorem not_loem_not_p : forall (P : Prop),
  ~ (P \/ ~P) -> ~P.
Proof.
  intros P not_loem p.
  set (F := not_loem (@or_introl P (~P) p)).
  contradiction.
Qed.

Theorem not_loem_not_not_p : forall (P : Prop),
  ~ (P \/ ~P) -> ~~P.
Proof.
  intros P not_loem notp.
  set (F := not_loem (@or_intror P (~P) notp)).
  contradiction.
Qed.

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~P).
Proof.
  intros P not_loem.
  set (notp := not_loem_not_p P not_loem).
  set (notnotp := not_loem_not_not_p P not_loem).
  contradiction.
Qed.

Definition excluded_middle := forall P : Prop, P \/ ~P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros loem X P nenpx x. unfold excluded_middle in loem.
  destruct (@loem (P x)) as [pxt | pxf].
  - apply pxt.
  - set (F := ex_intro (fun x => ~ P x) x pxf).
    contradiction.
Qed.

(* first 5 star exercise in the book *)
(* I proof a circular inference of the five propositions *)
(* which leads to a conclusion that they are equivalent *)

Definition peirce                : Prop :=
  forall P Q : Prop, ((P -> Q) -> P) -> P.
Definition double_negation_elim  : Prop :=
  forall P   : Prop, ~ ~ P -> P.
Definition de_morgan_not_and_not : Prop :=
  forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q.
Definition implies_to_or         : Prop :=
  forall P Q : Prop, (P -> Q) -> (~ P \/ Q).

Theorem contraposive2 :
  forall {P Q : Prop}, excluded_middle -> (~Q -> ~P) -> P -> Q.
Proof.
  intros P Q loem notp_notq q.
  destruct (@loem Q) as [pt | pf].
  - apply pt.
  - apply notp_notq in pf. contradiction.
Qed.

Theorem excluded_middle_peirce :
  excluded_middle -> peirce.
Proof.
  intros loem P Q pqp.
  destruct (@loem P) as [pt | pf].
  - apply pt.
  - set (pq := @contraposive2 P Q loem (fun _ => pf)).
    apply pqp in pq. contradiction.
Qed.

Theorem peirce_double_negation_elim :
  peirce -> double_negation_elim.
Proof.
  unfold peirce. intros peirc P notnotp.
  assert ((P -> False) -> P) as H.
  - intro pf. apply notnotp in pf. contradiction.
  - apply peirc in H. apply H.
Qed.

Theorem double_negation_elim_de_morgan_not_and_not :
  double_negation_elim -> de_morgan_not_and_not.
Proof.
  unfold double_negation_elim. intros dne P Q not_notp_and_notq.
  assert (forall P : Prop, P \/ ~P) as loem.
  - intro P0. apply dne. apply excluded_middle_irrefutable.
  - destruct (@loem P) as [p | notp]; destruct (@loem Q) as [q | notq].
    + left. apply p.
    + left. apply p.
    + right. apply q.
    + set (notp_notq := conj notp notq). contradiction.
Qed.

Theorem de_morgan_not_and_not_implies_to_or :
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not. intros de_morgan P Q pq.
  assert (forall P : Prop, P \/ ~P) as loem.
  - intro P0. apply de_morgan. intros [notp notnotp]. contradiction.
  - destruct (@loem P) as [pt | pf].
    + right. apply pq. apply pt.
    + left. apply pf.
Qed.

Theorem implies_to_or_excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  unfold implies_to_or. intros ito P.
  apply or_comm. apply ito. intro p. apply p.
Qed.
