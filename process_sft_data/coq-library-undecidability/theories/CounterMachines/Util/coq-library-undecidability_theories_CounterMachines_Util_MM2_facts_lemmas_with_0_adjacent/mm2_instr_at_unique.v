Require Import List Arith Lia.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition mm2_config : Set := (nat*(nat*nat)).

Lemma mm2_instr_at_unique {P: list mm2_instr} {i op op'} : mm2_instr_at op i P -> mm2_instr_at op' i P -> op = op'.
Proof.
move=> [l] [r] [+ +] [l'] [r'] => -> <- [+ ?] => /(f_equal (skipn (length l))).
have Hll': length l = length l' by lia.
by rewrite ?skipn_app ?[in RHS] Hll' ?Nat.sub_diag ?skipn_all => [[]].
