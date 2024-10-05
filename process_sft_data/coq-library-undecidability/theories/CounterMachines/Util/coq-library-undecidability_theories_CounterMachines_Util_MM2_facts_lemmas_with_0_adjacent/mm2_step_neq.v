Require Import List Arith Lia.
Import ListNotations.
Require Import Undecidability.MinskyMachines.MM2.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition mm2_config : Set := (nat*(nat*nat)).

Lemma mm2_step_neq {P: list mm2_instr} {x y: mm2_config} : mm2_step P x y -> x <> y.
Proof.
by move=> [[||j|j]] [_ +]; (case=> * []; lia).
