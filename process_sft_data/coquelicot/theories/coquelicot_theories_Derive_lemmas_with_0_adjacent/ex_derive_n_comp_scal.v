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

Lemma ex_derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> ex_derive_n (fun y => f (a * y)) n x.
Proof.
case: n f x => /= [ | n] f x Hf.
by [].
case: (Req_dec a 0) => Ha.
rewrite Ha => {a Ha Hf}.
apply ex_derive_ext with (fun _ => Derive_n (fun y : R => f (0 * y)) n 0).
elim: n => /= [ | n IH] t.
by rewrite ?Rmult_0_l.
rewrite -?(Derive_ext _ _ _ IH).
by rewrite ?Derive_const.
by apply ex_derive_const.
apply ex_derive_ext_loc with (fun x => a^n * Derive_n f n (a * x)).
case: Hf => r Hf.
have Hr0 : 0 < r / Rabs a.
apply Rdiv_lt_0_compat.
by apply r.
by apply Rabs_pos_lt.
exists (mkposreal _ Hr0) => /= y Hy.
apply eq_sym, Derive_n_comp_scal.
have : Rabs (a*y - a*x) < r.
rewrite -Rmult_minus_distr_l Rabs_mult.
replace (pos r) with (Rabs a * (r / Rabs a)) by (field ; by apply Rgt_not_eq, Rabs_pos_lt).
apply Rmult_lt_compat_l.
by apply Rabs_pos_lt.
by apply Hy.
move => {Hy} Hy.
apply Rabs_lt_between' in Hy ; case: Hy => Hy1 Hy2.
apply Rlt_Rminus in Hy1.
apply Rlt_Rminus in Hy2.
exists (mkposreal _ (Rmin_pos _ _ Hy1 Hy2)) => /= z Hz k Hk.
rewrite /ball /= /AbsRing_ball /= in Hz.
apply Rabs_lt_between' in Hz ; case: Hz => Hz1 Hz2.
rewrite /Rminus -Rmax_opp_Rmin in Hz1.
rewrite Rplus_min_distr_l in Hz2.
apply Rlt_le_trans with (2 := Rmin_r _ _) in Hz2.
ring_simplify in Hz2.
rewrite Rplus_max_distr_l in Hz1.
apply Rle_lt_trans with (1 := Rmax_l _ _) in Hz1.
ring_simplify in Hz1.
apply Hf.
apply Rabs_lt_between' ; by split.
by intuition.
apply ex_derive_scal.
apply ex_derive_comp.
apply (locally_singleton _ _) in Hf.
by apply Hf with (k := S n).
apply (ex_derive_scal id a x (ex_derive_id _)).
