Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma stepI {srs u v a b c d s t} : s = (u ++ a :: b :: v) -> t = (u ++ c :: d :: v) -> In ((a, b), (c, d)) srs -> step srs s t.
Proof.
move=> -> ->.
by constructor.
