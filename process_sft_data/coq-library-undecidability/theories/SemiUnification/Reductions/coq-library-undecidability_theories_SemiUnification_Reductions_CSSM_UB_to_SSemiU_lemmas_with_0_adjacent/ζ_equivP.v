Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Undecidability.StackMachines Require Import SSM.
From Undecidability.StackMachines.Util Require Import CSSM_facts.
Require Import Undecidability.SemiUnification.SemiU.
From Undecidability.SemiUnification.Util Require Import Facts Enumerable.
Require Import ssreflect ssrfun ssrbool.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Definition embed : config -> nat := to_nat.
Definition unembed : nat -> config := of_nat.
Definition embedP {X: config} : (unembed (embed X) = X) := enumP.
Definition SM_to_SUcs (M: ssm) : list constraint := map (fun '(x, y, a, b, d) => if d then ((a, embed ([], [], x)), (embed ([], [], y), b)) (* ax -> yb *) else ((b, embed ([], [], y)), (embed ([], [], x), a)) (* xa -> by *) ) M.
Section SM.
Context {M : ssm}.
Variable confluent_M : confluent M.
Notation equiv := (@equiv M).
Notation equiv_dec := (@equiv_dec M).
Notation narrow_dec := (@narrow_dec M).
Notation bounded' := (@bounded' M).
Fixpoint nf_aux (i: nat) (X: config) : config := match i with | 0 => X | S i => if equiv_dec (unembed i) X then nf_aux i (unembed i) else nf_aux i X end.
Definition nf (X: config) : config := nf_aux (embed X) X.
Fixpoint ζ (n: nat) (X: config) : term := match n with | 0 => atom (embed (nf X)) | S n => match X with | (A, B, x) => if narrow_dec (A, B, x) then arr (ζ n (A, B++[false], x)) (ζ n (A, B++[true], x)) else atom (embed (nf X)) end end.
Definition ψ (a: bool) (n: nat) (i: nat): term := match unembed i with | (A, B, x) => ζ (n - length B) (A++[a], B, x) end.
End SM.
Fixpoint term_depth_bound (t: term) : nat := match t with | atom _ => 1 | arr s t => 1 + (term_depth_bound s) + (term_depth_bound t) end.
Fixpoint depth_bound (φ: valuation) (xs: list state) : nat := match xs with | [] => 1 | x :: xs => 1 + term_depth_bound (φ x) + depth_bound φ xs end.
Fixpoint descend (t: term) (B: stack) {struct B} : option term := match B with | [] => Some t | b :: B => match t with | atom _ => None | arr s t => descend (if b then t else s) B end end.
Fixpoint ascend (ψ0 ψ1: valuation) (t: term) (A: stack) : term := match A with | [] => t | a :: A => ascend ψ0 ψ1 (substitute (if a then ψ1 else ψ0) t) A end.
Definition interpret (φ ψ0 ψ1: valuation) (X: config) : option term := match X with | (A, B, x) => descend (ascend ψ0 ψ1 (φ (embed ([], [], x))) A) B end.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma ζ_equivP {n: nat} {x x': state} {A B A' B': stack} : bounded' n -> equiv (A, B, x) (A', B', x') -> ζ (S n - length B) (A, B, x) = ζ (S n - length B') (A', B', x').
Proof using confluent_M.
move /(extend_bounded' confluent_M) => Hn.
move Hm: (S n - length B)=> m.
elim: m A B A' B' Hm.
-
move=> A B A' B' HnB Hxx'.
have [-> | HnB']: (S n - length B' = 0 \/ S n - length B' = (S (n - length B'))) by lia.
{
rewrite ? ζ_0P.
do 2 f_equal.
by apply: nf_equiv_eq.
}
rewrite HnB' ζ_0P ζ_SnP.
case: (narrow_dec (A', B', x')) => /=; first last.
{
move=> _.
do 2 f_equal.
by apply: nf_equiv_eq.
}
move /equiv_sym in Hxx'.
move /(narrow_equiv confluent_M Hxx') /Hn => /=.
by lia.
-
move=> m IH A B A' B' Hm Hxx'.
have [HnB' | ->]: (S n - length B' = 0 \/ S n - length B' = S (n - length B')) by lia.
{
rewrite HnB' ζ_0P ζ_SnP.
case: (narrow_dec (A, B, x)) => /=; first last.
-
move=> _.
do 2 f_equal.
by apply: nf_equiv_eq.
-
move /(narrow_equiv confluent_M Hxx') /Hn => /=.
by lia.
}
rewrite ?ζ_SnP.
case: (narrow_dec (A, B, x)); case: (narrow_dec (A', B', x'))=> /=.
+
move=> _ _.
apply: (arr_eqI (s := fun=> ζ _ _) (t := fun=> ζ _ _)).
move=> b.
have -> : n - length B' = S n - length (B' ++ [b]) by (rewrite app_length /length; lia).
apply: IH; [ rewrite app_length /length -/(length _); by lia | by apply: equiv_appR].
+
by move=> + /(narrow_equiv confluent_M Hxx').
+
by move=> /(narrow_equiv confluent_M ((iffLR equiv_sym) Hxx')).
+
move=> _ _.
do 2 f_equal.
by apply: nf_equiv_eq.
