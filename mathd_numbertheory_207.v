
(*Require Import Lia.这个加上本地coqpyt报错 但是jscoq没有报错*)
Lemma sfft_factor :
  forall (x y : nat),
    (0 < y) ->
    (y < x) ->
    (x + y + (x * y) = 80) -> ((x + 1) * (y+1) = 81).
Proof.

