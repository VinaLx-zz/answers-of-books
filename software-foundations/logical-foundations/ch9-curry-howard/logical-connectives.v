Require Import Utf8.
Require Import Even.

Definition conj_fact : ∀P Q R, P ∧ Q → Q ∧ R → P ∧ R :=
  fun P Q R pq qr => match pq, qr with
  | conj p _, conj _ r => conj p r
  end.

Definition or_comm : ∀P Q, P ∨ Q → Q ∨ P :=
  fun P Q p_or_q => match p_or_q with
  | or_introl p => or_intror p
  | or_intror q => or_introl q
  end.

Definition ex_ev_Sn : ex (fun n => even (S n)) :=
  ex_intro (fun n => even (S n)) 1 (even_S 1 (odd_S 0 (even_O))).

