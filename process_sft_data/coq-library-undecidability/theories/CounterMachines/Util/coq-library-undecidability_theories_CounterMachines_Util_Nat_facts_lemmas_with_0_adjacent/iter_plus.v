Require Import PeanoNat Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments measure_ind {X}.
Definition nat_norm := (Nat.add_0_r, Nat.add_succ_r, Nat.sub_0_r, Nat.mul_1_r, Nat.div_1_r).

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
by rewrite Nat.add_comm /Nat.iter nat_rect_plus.
