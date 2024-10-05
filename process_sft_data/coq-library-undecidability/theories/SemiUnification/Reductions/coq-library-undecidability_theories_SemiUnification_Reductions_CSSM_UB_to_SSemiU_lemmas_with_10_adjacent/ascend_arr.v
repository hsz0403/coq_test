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

Lemma nf_equiv_eq (X Y: config) : equiv X Y -> nf X = nf Y.
Proof using confluent_M.
have: (embed X = embed Y \/ embed X < embed Y \/ embed Y < embed X) by lia.
case; [|case].
-
move /(f_equal unembed).
rewrite ? embedP.
by move=> ->.
-
move=> + H.
move /nf_equiv_eq_ind.
by move /(_ _ H).
-
move=> + /equiv_sym H.
move /nf_equiv_eq_ind.
Admitted.

Lemma ζ_nilP {n: nat} {x: state} : ζ (S n) ([], [], x) = arr (ζ n ([], [false], x)) (ζ n ([], [true], x)).
Proof.
move=> /=.
case: (narrow_dec ([], [], x)); first done.
move=> H.
exfalso.
apply: H.
exists x, [].
Admitted.

Lemma ζ_0P {X: config} : ζ 0 X = atom (embed (nf X)).
Proof.
Admitted.

Lemma ζ_SnP {n: nat} {x: state} {A B: stack} : ζ (S n) (A, B, x) = if narrow_dec (A, B, x) then arr (ζ n (A, B++[false], x)) (ζ n (A, B++[true], x)) else atom (embed (nf (A, B, x))).
Proof.
Admitted.

Lemma SM_to_SUcsP {x y: state} {a b: symbol} : In (a, x, (y, b)) (SM_to_SUcs M) -> exists x' y', x = (embed ([], [], x')) /\ y = (embed ([], [], y')) /\ equiv ([a], [], x') ([], [b], y').
Proof.
rewrite /SM_to_SUcs in_map_iff.
move=> [[[[[x' y'] a'] b'] d]].
case: d.
-
case.
case=> <- <- <- <- H.
exists x', y'.
constructor; first done.
constructor; first done.
exists ([], [b'], y').
constructor; [apply: rt_step; by apply: step_l | by apply: rt_refl].
-
case.
case=> <- <- <- <- H.
exists y', x'.
constructor; first done.
constructor; first done.
exists ([b'], [], y').
Admitted.

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
Admitted.

Lemma ψP {a: bool} {n: nat} {X: config} : ψ a n (embed X) = match X with | (A, B, x) => ζ (n - length B) (A++[a], B, x) end.
Proof.
Admitted.

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
Admitted.

Lemma soundness {M: cssm} : CSSM_UB M -> SSemiU (SM_to_SUcs (proj1_sig M)).
Proof.
Opaque ζ ψ.
case: M=> M confluent_M.
rewrite /CSSM_UB /SSemiU.
move /(boundedP confluent_M) => /= [n HnM].
exists (fun i => @ζ M (S n) (unembed i)), (@ψ M false (S n)), (@ψ M true (S n)).
move=> [[a x]] => [[y b]] /=.
move /SM_to_SUcsP => [x' [y' [-> [->]]]] /equiv_sym Hxy.
rewrite ?embedP ζ_nilP (itebP (P := fun _ => ζ _ _)).
have /= := ζ_equivP confluent_M HnM Hxy.
have ->: n - 0 = n by lia.
move=> ->.
rewrite (itebP (P := fun=> ψ _ _)).
Admitted.

Lemma depth_boundP {φ: valuation} {x: state} {xs: list state} : In x xs -> term_depth_bound (φ x) <= depth_bound φ xs.
Proof.
elim: xs; first done.
Admitted.

Lemma interpretP {M: ssm} {X Y: config} {φ ψ0 ψ1: valuation} : Forall (models φ ψ0 ψ1) (SM_to_SUcs M) -> reachable M X Y -> interpret φ ψ0 ψ1 X = interpret φ ψ0 ψ1 Y.
Proof.
move=> HM.
elim; [| done | by move=> > ? ->].
move=> {}X {}Y [|] x y a b A B.
-
move: HM.
rewrite /SM_to_SUcs Forall_mapP Forall_forall => HM.
move /HM.
rewrite /models /interpret.
case: (φ (embed ([], [], y))); first done.
move: a b => [|] [|] ? ? -> /=; by rewrite ascend_arr.
-
move: HM.
rewrite /SM_to_SUcs Forall_mapP Forall_forall => HM.
move /HM.
rewrite /models /interpret.
case: (φ (embed ([], [], x))); first done.
Admitted.

Lemma descendP {s t: term} {B: list symbol} : descend s B = Some t -> length B <= term_depth_bound s.
Proof.
elim: B s t; first by (move=> /= *; lia).
Admitted.

Lemma completeness {M: cssm}: SSemiU (SM_to_SUcs (proj1_sig M)) -> CSSM_UB M.
Proof.
case: M=> M confluent_M /=.
move=> [φ [ψ0 [ψ1]]].
rewrite -Forall_forall => Hφ.
pose f x := embed (([], [], x) : config).
apply: (bounded_of_bounded' confluent_M (n := depth_bound φ (map f (enum_states M)))).
move=> /= Z x y A B Hx Hy.
case: (In_dec _ y (enum_states M)); first by decide equality.
{
move=> /(in_map f) /depth_boundP => /(_ φ) Hfy.
move: Hy => /(interpretP Hφ).
move: Hx => /(interpretP Hφ) <- /= /descendP.
rewrite -/(f y).
move: (length B) => ?.
by lia.
}
move: (Hy) Hx => /enum_states_reachable [<- /enum_states_reachable | ]; last by by move=> [+].
case; last by move=> [+].
case=> *.
subst=> /=.
Admitted.

Theorem reduction : CSSM_UB ⪯ SSemiU.
Proof.
exists (fun dM => Argument.SM_to_SUcs (proj1_sig dM)).
intros [M HM].
constructor.
-
exact Argument.soundness.
-
Admitted.

Lemma ascend_arr {ψ0 ψ1: valuation} {s t: term} {A: stack} : ascend ψ0 ψ1 (arr s t) A = arr (ascend ψ0 ψ1 s A) (ascend ψ0 ψ1 t A).
Proof.
elim: A s t; first done.
move=> a A IH s t /=.
by rewrite IH.
