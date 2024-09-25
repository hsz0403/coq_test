
From Coq Require Import Lia.

(*Require Import Lia.*)
Theorem amc12a_2015_p10 :
  forall (x y : nat),
    (0 < y) ->
    (y < x) ->
    (x + y + (x * y) = 80) ->
    x = 26.
Proof.

