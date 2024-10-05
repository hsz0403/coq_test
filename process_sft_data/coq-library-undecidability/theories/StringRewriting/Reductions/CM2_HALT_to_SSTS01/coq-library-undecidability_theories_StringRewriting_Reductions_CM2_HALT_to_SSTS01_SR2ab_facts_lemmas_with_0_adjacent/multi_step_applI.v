Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma multi_step_applI {srs u s t} : multi_step srs s t -> multi_step srs (u ++ s) (u ++ t).
Proof.
move=> /multi_step_appI => /(_ u []).
by rewrite ?app_nil_r.
