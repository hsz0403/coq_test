Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma sym_eq_dec (x y: Symbol) : {x = y} + {x <> y}.
Proof.
by do 3 (decide equality).
