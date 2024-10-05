Require Import List Arith Lia.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition mm2_config : Set := (nat*(nat*nat)).

Lemma mm2_instr_at_bounds {P: list mm2_instr} {mmi: mm2_instr} {i: nat} : mm2_instr_at mmi i P -> 0 < i /\ i <= length P.
Proof.
move=> [l] [r] [-> <-].
rewrite app_length /=.
by lia.
