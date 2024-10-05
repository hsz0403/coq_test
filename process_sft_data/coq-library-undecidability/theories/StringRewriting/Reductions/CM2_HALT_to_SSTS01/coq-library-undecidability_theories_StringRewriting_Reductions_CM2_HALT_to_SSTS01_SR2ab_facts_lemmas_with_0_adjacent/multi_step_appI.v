Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma multi_step_appI {srs u v s t} : multi_step srs s t -> multi_step srs (u ++ s ++ v) (u ++ t ++ v).
Proof.
elim; [| move=> *; by apply: rt_refl | move=> *; apply: rt_trans; by eassumption ].
move=> {}s {}t [] u' v' > ?.
apply /rt_step /(stepI (u := u ++ u') (v := v' ++ v)); last by eassumption.
all: by rewrite -?app_assoc.
