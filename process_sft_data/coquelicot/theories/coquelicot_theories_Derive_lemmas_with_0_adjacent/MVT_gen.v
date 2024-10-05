Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Lim_seq Iter.
Require Import Hierarchy Continuity Equiv.
Open Scope R_scope.
Section LinearFct.
Context {K : AbsRing} {U V : NormedModule K}.
Record is_linear (l : U -> V) := { linear_plus : forall (x y : U), l (plus x y) = plus (l x) (l y) ; linear_scal : forall (k : K) (x : U), l (scal k x) = scal k (l x) ; linear_norm : exists M : R, 0 < M /\ (forall x : U, norm (l x) <= M * norm x) }.
End LinearFct.
Section Op_LinearFct.
Context {K : AbsRing} {V : NormedModule K}.
End Op_LinearFct.
Section Linear_domin.
Context {T : Type} {Kw K : AbsRing} {W : NormedModule Kw} {U V : NormedModule K}.
End Linear_domin.
Section Diff.
Context {K : AbsRing} {U : NormedModule K} {V : NormedModule K}.
Definition filterdiff (f : U -> V) F (l : U -> V) := is_linear l /\ forall x, is_filter_lim F x -> is_domin F (fun y : U => minus y x) (fun y => minus (minus (f y) (f x)) (l (minus y x))).
Definition ex_filterdiff (f : U -> V) F := exists (l : U -> V), filterdiff f F l.
End Diff.
Section Diff_comp.
Context {K : AbsRing} {U V W : NormedModule K}.
End Diff_comp.
Section Diff_comp2.
Context {K : AbsRing} {T U V : NormedModule K}.
Section Diff_comp2'.
Context {W : NormedModule K}.
End Diff_comp2'.
Context {W : NormedModule K}.
End Diff_comp2.
Section Operations.
Context {K : AbsRing} {V : NormedModule K}.
Local Ltac plus_grab e := repeat rewrite (plus_assoc _ e) -(plus_comm e) -(plus_assoc e).
End Operations.
Section Operations_fct.
Context {K : AbsRing} {U V : NormedModule K}.
End Operations_fct.
Section Derive.
Context {K : AbsRing} {V : NormedModule K}.
Definition is_derive (f : K -> V) (x : K) (l : V) := filterdiff f (locally x) (fun y : K => scal y l).
Definition ex_derive (f : K -> V) (x : K) := exists l : V, is_derive f x l.
End Derive.
Definition Derive (f : R -> R) (x : R) := real (Lim (fun h => (f (x+h) - f x)/h) 0).
Section Extensionality.
Context {K : AbsRing} {V : NormedModule K}.
End Extensionality.
Section Const.
Context {K : AbsRing} {V : NormedModule K}.
End Const.
Section Id.
Context {K : AbsRing}.
End Id.
Section Opp.
Context {K : AbsRing} {V : NormedModule K}.
End Opp.
Section Plus.
Context {K : AbsRing} {V : NormedModule K}.
End Plus.
Section Minus.
Context {K : AbsRing} {V : NormedModule K}.
End Minus.
Section Scal_l.
Context {K : AbsRing} {V : NormedModule K}.
End Scal_l.
Section Comp.
Context {K : AbsRing} {V : NormedModule K}.
End Comp.
Section ext_cont.
Context {U : UniformSpace}.
Definition extension_cont (f g : R -> U) (a x : R) : U := match Rle_dec x a with | left _ => f x | right _ => g x end.
End ext_cont.
Section ext_cont'.
Context {V : NormedModule R_AbsRing}.
End ext_cont'.
Section ext_C0.
Context {V : NormedModule R_AbsRing}.
Definition extension_C0 (f : R -> V) (a b : Rbar) (x : R) : V := match Rbar_le_dec a x with | left _ => match Rbar_le_dec x b with | left _ => f x | right _ => f (real b) end | right _ => f (real a) end.
End ext_C0.
Section ext_C1.
Context {V : NormedModule R_AbsRing}.
Definition extension_C1 (f df : R -> V) (a b : Rbar) (x : R) : V := match Rbar_le_dec a x with | left _ => match Rbar_le_dec x b with | left _ => f x | right _ => plus (f (real b)) (scal (x - real b) (df (real b))) end | right _ => plus (f (real a)) (scal (x - real a) (df (real a))) end.
End ext_C1.
Section NullDerivative.
Context {V : NormedModule R_AbsRing}.
End NullDerivative.
Fixpoint Derive_n (f : R -> R) (n : nat) x := match n with | O => f x | S n => Derive (Derive_n f n) x end.
Definition ex_derive_n f n x := match n with | O => True | S n => ex_derive (Derive_n f n) x end.
Definition is_derive_n f n x l := match n with | O => f x = l | S n => is_derive (Derive_n f n) x l end.

Lemma MVT_gen (f : R -> R) (a b : R) (df : R -> R) : let a0 := Rmin a b in let b0 := Rmax a b in (forall x, a0 < x < b0 -> is_derive f x (df x)) -> (forall x, a0 <= x <= b0 -> continuity_pt f x) -> exists c, a0 <= c <= b0 /\ f b - f a = df c * (b - a).
Proof.
move => a0 b0 Hd Hf.
case: (Req_dec a0 b0) => Hab.
exists a0 ; split.
split ; by apply Req_le.
replace b with a.
ring.
move: Hab ; rewrite /a0 /b0 /Rmin /Rmax ; by case: Rle_dec => Hab.
have pr1 : forall c:R, a0 < c < b0 -> derivable_pt f c.
move => x Hx ; exists (df x).
by apply is_derive_Reals, Hd.
have pr2 : forall c:R, a0 < c < b0 -> derivable_pt id c.
move => x Hx ; exists 1.
by apply derivable_pt_lim_id.
case: (MVT f id a0 b0 pr1 pr2).
apply Rnot_le_lt ; contradict Hab ; apply Rle_antisym.
by apply Rcomplements.Rmin_Rmax.
by apply Hab.
by apply Hf.
move => x Hx ; apply derivable_continuous, derivable_id.
move => /= c [Hc H].
exists c ; split.
split ; by apply Rlt_le, Hc.
replace (df c) with (derive_pt f c (pr1 c Hc)).
move: H ; rewrite {1 2}/id /a0 /b0 /Rmin /Rmax ; case: Rle_dec => Hab0 H.
rewrite Rmult_comm H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
ring.
replace (derive_pt f c (pr1 c Hc) * (b - a)) with (-((a - b) * derive_pt f c (pr1 c Hc))) by ring.
rewrite H -(pr_nu _ _ (derivable_pt_id _)) derive_pt_id.
ring.
case: (pr1 c Hc) => /= l Hl.
transitivity (Derive f c).
apply sym_eq, is_derive_unique, is_derive_Reals, Hl.
by apply is_derive_unique, Hd.
