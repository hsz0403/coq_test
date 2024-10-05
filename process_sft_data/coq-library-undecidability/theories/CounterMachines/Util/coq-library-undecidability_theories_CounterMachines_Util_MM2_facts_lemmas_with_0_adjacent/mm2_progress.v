Require Import List Arith Lia.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition mm2_config : Set := (nat*(nat*nat)).

Lemma mm2_progress {mmi: mm2_instr} {x: mm2_config} : exists y, mm2_atom mmi x y.
Proof.
move: x mmi => [i [[|a] [|b]]] [||j|j]; eexists; by constructor.
