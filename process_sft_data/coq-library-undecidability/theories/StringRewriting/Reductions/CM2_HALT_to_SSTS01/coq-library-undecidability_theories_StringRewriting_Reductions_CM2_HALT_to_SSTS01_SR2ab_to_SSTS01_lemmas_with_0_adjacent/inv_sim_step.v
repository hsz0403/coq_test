Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import Undecidability.StringRewriting.SSTS.
Require Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab_facts.
Require Import Undecidability.StringRewriting.Util.List_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Local Arguments rt_trans {A R x y z}.
Definition enc_pair '(x, y) : nat := (x + y) * (x + y) + y.
Opaque enc_pair.
Module Argument.
Section Reduction.
Context (srs : Srs) (a0: Symbol) (b0: Symbol) (Ha0b0: b0 <> a0).
Import SR2ab_facts (sym_eq_dec).
Definition enc (x: Symbol) : nat := if sym_eq_dec x a0 then 0 else if sym_eq_dec x b0 then 1 else 2 + ( match x with | (n, None) => enc_pair (n, 0) | (n, Some m) => enc_pair (n, 1 + m) end).
Definition ssts : Ssts := map (fun '((a, b), (c, d)) => ((enc a, enc b), (enc c, enc d))) srs.
End Reduction.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma inv_sim_step {s t'} : SSTS.step ssts (map enc s) t' -> exists t, t' = map enc t /\ SR2ab.step srs s t.
Proof.
move Hs': (map enc s) => s' Hs't'.
case: Hs't' Hs' => u' v' a' b' c' d' H Hs.
move: H.
rewrite /ssts in_map_iff.
move=> [[[a b]]] [c d] [[]] ? ? ? ?.
subst.
move=> H.
exists (firstn (length u') s ++ c :: d :: skipn (length u' + 2) s).
constructor.
-
rewrite map_app /= map_firstn map_skipn Hs.
rewrite firstn_app (ltac:(lia) : length u' - length u' = 0) firstn_all.
rewrite skipn_app (ltac:(lia) : length u' + 2 - length u' = 2) skipn_all2 /=; first by lia.
by rewrite app_nil_r.
-
move: H => /SR2ab_facts.stepI.
apply; last done.
apply: map_enc_inj.
rewrite Hs map_app /= map_firstn map_skipn Hs.
rewrite firstn_app (ltac:(lia) : length u' - length u' = 0) firstn_all.
rewrite skipn_app (ltac:(lia) : length u' + 2 - length u' = 2) skipn_all2 /=; first by lia.
by rewrite app_nil_r.
