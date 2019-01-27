Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros [|n'] [|m']; split
  ;try reflexivity ;try discriminate H.
Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros p q [p' q'].
  apply q'.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.

Example not_implies_our_not : forall (P:Prop),
  ~P -> (forall Q:Prop, P -> Q).
Proof.
  intros P contra q p.
  contradiction.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q pq notq p.
  apply pq in p. contradiction.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros p [].
  contradiction.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
  - intros [p | [q r]].
    + split; left; apply p.
    + split; right. apply q. apply r.
  - intros [[p | q] [p' | r]].
    + left. apply p.
    + left. apply p.
    + left. apply p'.
    + right. apply (conj q r).
Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros. intros [x notpx].
  apply notpx in H.
  contradiction.
Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros [x [px | qx]].
    + left. exists x. apply px.
    + right. exists x. apply qx.
  - intros [[x px] | [x qx]].
    + exists x. left. apply px.
    + exists x. right. apply qx.
Qed.

