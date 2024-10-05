Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import ssreflect.
Set Default Goal Selector "!".

Lemma sym_eq_dec (x y: Symbol) : {x = y} + {x <> y}.
Proof.
Admitted.

Lemma stepI {srs u v a b c d s t} : s = (u ++ a :: b :: v) -> t = (u ++ c :: d :: v) -> In ((a, b), (c, d)) srs -> step srs s t.
Proof.
move=> -> ->.
Admitted.

Lemma multi_step_appI {srs u v s t} : multi_step srs s t -> multi_step srs (u ++ s ++ v) (u ++ t ++ v).
Proof.
elim; [| move=> *; by apply: rt_refl | move=> *; apply: rt_trans; by eassumption ].
move=> {}s {}t [] u' v' > ?.
apply /rt_step /(stepI (u := u ++ u') (v := v' ++ v)); last by eassumption.
Admitted.

Lemma multi_step_apprI {srs v s t} : multi_step srs s t -> multi_step srs (s ++ v) (t ++ v).
Proof.
Admitted.

Lemma multi_step_applI {srs u s t} : multi_step srs s t -> multi_step srs (u ++ s) (u ++ t).
Proof.
move=> /multi_step_appI => /(_ u []).
by rewrite ?app_nil_r.
