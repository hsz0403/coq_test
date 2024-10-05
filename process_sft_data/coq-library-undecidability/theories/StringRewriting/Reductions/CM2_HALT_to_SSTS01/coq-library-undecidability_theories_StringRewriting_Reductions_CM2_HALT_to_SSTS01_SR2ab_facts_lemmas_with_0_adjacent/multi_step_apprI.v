Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma multi_step_apprI {srs v s t} : multi_step srs s t -> multi_step srs (s ++ v) (t ++ v).
Proof.
by move=> /multi_step_appI => /(_ [] v).
