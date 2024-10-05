Require Import List Arith Lia.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition mm2_config : Set := (nat*(nat*nat)).

Lemma mm2_mmi_lookup {P: list mm2_instr} {i: nat} : i < length P -> exists (mmi : mm2_instr), P = firstn i P ++ mmi :: skipn (1+i) P.
Proof.
elim: i P.
{
move=> [|mmi' P'] /=; first by lia.
move=> _.
by eexists.
}
move=> i IH [|mmi' P'] /=; first by lia.
move /Lt.lt_S_n /IH => [? ?].
eexists.
f_equal.
by eassumption.
