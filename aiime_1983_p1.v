(*
 * Author: Talia Ringer, refined by Gaëtan Gilbert 
 *
 * We should probably move to SSReflect for the rest of these theorems & proofs,
 * and revisit this proof once we are on SSReflect
 *)
Require Import Reals Lra Lia.
Infix "/" := Rdiv.
Infix "+" := Rplus.
Infix "*" := Rmult.
Infix "-" := Rminus.

(*
 * Lift ln to nats
 *)
Definition ln (n : nat) : R :=
  ln (INR n).

(*
 * Lift ln lemmas to nats
 *)
Lemma ln_mult :
  forall x y : nat,
    0 < x ->
    0 < y ->
    ln (x * y) = ln x + ln y.
Proof.

