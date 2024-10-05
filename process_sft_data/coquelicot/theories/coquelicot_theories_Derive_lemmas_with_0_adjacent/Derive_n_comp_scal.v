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

Lemma Derive_n_comp_scal (f : R -> R) (a : R) (n : nat) (x : R) : locally (a * x) (fun x => forall k, (k <= n)%nat -> ex_derive_n f k x) -> Derive_n (fun y => f (a * y)) n x = (a ^ n * Derive_n f n (a * x)).
Proof.
case: (Req_dec a 0) => [ -> _ | Ha] /=.
rewrite Rmult_0_l.
elim: n x => [ | n IH] x /= ; rewrite ?Rmult_0_l.
ring.
rewrite (Derive_ext _ _ _ IH).
by apply Derive_const.
move => Hf.
apply (locally_singleton _ (fun x => Derive_n (fun y : R => f (a * y)) n x = a ^ n * Derive_n f n (a * x))).
elim: n Hf => [ | n IH] Hf.
apply filter_forall => /= y ; ring.
case: IH => [ | r IH].
case: Hf => r0 Hf.
exists r0 => y Hy k Hk ; by intuition.
case: Hf => r0 Hf.
have Hr1 : 0 < Rmin (r0 / (Rabs a)) r.
apply Rmin_case.
apply Rdiv_lt_0_compat.
by apply r0.
by apply Rabs_pos_lt.
by apply r.
set r1 := mkposreal _ Hr1.
exists r1 => y Hy /=.
rewrite (Derive_ext_loc _ (fun y => a ^ n * Derive_n f n (a * y))).
rewrite Derive_scal.
rewrite (Rmult_comm a (a^n)) Rmult_assoc.
apply f_equal.
rewrite Derive_comp.
rewrite (Derive_ext (Rmult a) (fun x => a * x)) => //.
rewrite Derive_scal Derive_id ; ring.
apply Hf with (k := S n).
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /=.
rewrite -/(Rminus _ _) -Rmult_minus_distr_l Rabs_mult.
apply Rlt_le_trans with (Rabs a * r1).
apply Rmult_lt_compat_l.
by apply Rabs_pos_lt.
by apply Hy.
rewrite Rmult_comm ; apply Rle_div_r.
by apply Rabs_pos_lt.
rewrite /r1 ; by apply Rmin_l.
by apply lt_n_Sn.
apply ex_derive_scal.
by apply ex_derive_id.
rewrite /ball /= /AbsRing_ball /= in Hy.
apply Rabs_lt_between' in Hy.
case: Hy => Hy1 Hy2.
apply Rlt_Rminus in Hy1.
apply Rlt_Rminus in Hy2.
have Hy : 0 < Rmin (y - (x - r1)) (x + r1 - y).
by apply Rmin_case.
exists (mkposreal (Rmin (y - (x - r1)) (x + r1 - y)) Hy).
set r2 := Rmin (y - (x - r1)) (x + r1 - y).
move => t Ht.
apply IH.
apply Rabs_lt_between'.
rewrite /ball /= /AbsRing_ball /= in Ht.
apply Rabs_lt_between' in Ht.
simpl in Ht.
split.
apply Rle_lt_trans with (2 := proj1 Ht).
rewrite /r2 ; apply Rle_trans with (y-(y-(x-r1))).
ring_simplify ; apply Rplus_le_compat_l, Ropp_le_contravar.
rewrite /r1 ; apply Rmin_r.
apply Rplus_le_compat_l, Ropp_le_contravar, Rmin_l.
apply Rlt_le_trans with (1 := proj2 Ht).
rewrite /r2 ; apply Rle_trans with (y+((x+r1)-y)).
apply Rplus_le_compat_l, Rmin_r.
ring_simplify ; apply Rplus_le_compat_l.
rewrite /r1 ; apply Rmin_r.
