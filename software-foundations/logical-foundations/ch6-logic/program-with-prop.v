Require Import List.
Import ListNotations.
Require Import Nat.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  split.
  - induction l as [| h t IH].
    + simpl. intros. contradiction.
    + simpl. intros [inh | int].
      * exists h. split. apply inh. left. reflexivity.
      * apply IH in int.
        destruct int as [xx [fxy inxt]].
        exists xx. split. apply fxy. right. apply inxt.
  - induction l as [| h t IH].
    + simpl. intros [x []]. contradiction.
    + simpl. intros [x [fxy [hx | inxt]]].
      * left. rewrite hx. apply fxy.
      * set (exi := ex_intro (fun x => f x = y /\ In x t) x (conj fxy inxt)).
        apply IH in exi. right. apply exi.
Qed.

Lemma In_app_iff : forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  split; induction l as [| h t IH].
  - simpl. intros. right. apply H.
  - simpl. intros [ha | intl'].
    + left. left. apply ha.
    + apply IH in intl'. apply or_assoc. right. apply intl'.
  - simpl. intros [|].
    + contradiction. + apply H.
  - simpl. intros [[ha | inat] | inal'].
    + left. apply ha.
    + set (ih := @or_introl (In a t) (In a l') inat).
      apply IH in ih. right. apply ih.
    + set (ih := @or_intror (In a t) (In a l') inal').
      apply IH in ih. right. apply ih.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Theorem remove_orl_infer : forall {T : Type} {PL PR PC : T -> Prop},
  (forall x : T, PL x \/ PR x -> PC x) -> (forall x : T, PR x -> PC x).
Proof.
  intros. apply H. right. apply H0.
Qed.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  split; induction l as [| h t IH]; simpl.
  - intros. apply I.
  - intros.
    set (hrefl := @or_introl (h = h) (In h t) (@eq_refl T h)).
    apply H in hrefl.
    set (ihh := remove_orl_infer H). apply IH in ihh.
    apply (conj hrefl ihh).
  - intros. contradiction.
  - intros [ph allpt] x [hx | inxt].
    + rewrite <- hx. apply ph.
    + set (ic := IH allpt x inxt). apply ic.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) (n : nat) : Prop :=
  if odd n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  unfold combine_odd_even.
  intros Podd Peven n oddt oddf.
  destruct (odd n) as [|] eqn:E.
  - apply (oddt eq_refl).
  - apply (oddf eq_refl).
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true -> Podd n.
Proof.
  unfold combine_odd_even.
  intros Podd Peven n oe ont.
  rewrite ont in oe. apply oe.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false -> Peven n.
Proof.
  unfold combine_odd_even.
  intros Podd Peven n oe onf.
  rewrite onf in oe.
  apply oe.
Qed.

