Require Import Even.

Theorem ev_8 : even 8.
Proof.
    repeat apply even_S || apply odd_S.
    apply even_O.
Qed.

Definition ev_8' : even 8 := even_S 7
  (odd_S 6
     (even_S 5 (odd_S 4 (even_S 3 (odd_S 2 (even_S 1 (odd_S 0 even_O))))))).

