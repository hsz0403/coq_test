Require Import List Arith Lia.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition mm2_config : Set := (nat*(nat*nat)).

Lemma mm2_step_or_halt (P: list mm2_instr) (x: mm2_config) : (exists y, mm2_step P x y) \/ (mm2_stop P x).
Proof.
move: x => [i [a b]].
have [? | [? ?]] : ((i = 0 \/ i > length P) \/ (1 <= i /\ i <= length P)) by lia.
{
right.
move=> y [? [/mm2_instr_at_bounds]] /=.
by lia.
}
have [mmi ?] := mm2_mmi_lookup (i := i-1) (P := P) ltac:(lia).
have [y Hy] := mm2_progress (mmi := mmi) (x := (i, (a, b))).
left.
exists y, mmi.
constructor; last done.
eexists.
eexists.
constructor; first by eassumption.
rewrite firstn_length_le /=; by lia.
