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

Lemma ψζP {n: nat} {x: state} {A B: stack} {a: bool} : bounded' n -> ζ (S n - length B) (A ++ [a], B, x) = substitute (ψ a (S n)) (ζ (S n - length B) (A, B, x)).
Proof using confluent_M.
move=> Hn.
move Hm: (S n - length B)=> m.
elim: m x A B Hm.
-
move=> x A B Hm.
rewrite ? ζ_0P /= ψP.
move HAxB: (nf (A, B, x)) => [[A' B'] x'].
have [-> | ?]: S n - length B' = 0 \/ S n - length B' > 0 by lia.
{
rewrite ζ_0P.
f_equal.
f_equal.
apply: nf_equiv_eq.
apply: equiv_appL.
rewrite -HAxB.
by apply: nf_equiv.
}
have Hxx': equiv (A' ++ [a], B', x') (A ++ [a], B, x).
{
apply: equiv_appL.
rewrite equiv_sym -HAxB.
by apply: nf_equiv.
}
by rewrite (ζ_equivP Hn Hxx') Hm ζ_0P.
-
move=> m IH x A B Hm.
rewrite ? ζ_SnP.
case: (narrow_dec (A, B, x)).
+
move=> /= /(narrow_appL (a := a)) => ?.
case: (narrow_dec (A ++ [a], B, x)); last done.
move=> _ /=.
apply: (arr_eqI (s := fun => ζ _ _) (t := fun => substitute _ _)).
move=> b.
apply: IH.
rewrite app_length /length -/(length _).
by lia.
+
move=> _ /=.
rewrite -(ζ_SnP (A := A ++ [a])).
rewrite ψP.
move HAxB: (nf (A, B, x)) => [[A' B'] x'].
rewrite -Hm.
have Hxx': equiv (A ++ [a], B, x) (A' ++ [a], B', x').
{
apply: equiv_appL.
rewrite -HAxB.
by apply: nf_equiv.
}
by rewrite (ζ_equivP Hn Hxx').
