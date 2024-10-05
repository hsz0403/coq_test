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

Lemma repeat_b0 {n} : repeat 1 n = map enc (repeat b0 n).
Proof using Ha0b0.
elim: n; first done.
move=> n /= ->.
congr cons.
rewrite /enc.
case: (sym_eq_dec b0 a0); [done | by case: (sym_eq_dec b0 b0)].
