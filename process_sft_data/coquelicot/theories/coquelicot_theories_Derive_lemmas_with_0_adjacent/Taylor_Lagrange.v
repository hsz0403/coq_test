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

Theorem Taylor_Lagrange : forall f n x y, x < y -> ( forall t, x <= t <= y -> forall k, (k <= S n)%nat -> ex_derive_n f k t ) -> exists zeta, x < zeta < y /\ f y = sum_f_R0 (fun m => (y-x) ^ m / INR (fact m) * Derive_n f m x ) n + (y-x) ^ (S n) / INR (fact (S n)) * Derive_n f (S n) zeta.
Proof.
intros f n x y Hxy Df.
pose (c:= (f y - sum_f_R0 (fun m => (y-x) ^ m / INR (fact m) * Derive_n f m x ) n) / (y-x) ^ (S n)).
pose (g t := f y - sum_f_R0 (fun m => (y-t) ^ m / INR (fact m) * Derive_n f m t ) n - c * (y-t) ^ (S n)).
assert (Dg : forall t, x <= t <= y -> is_derive g t (- (y-t) ^ n / INR (fact n) * Derive_n f (S n) t + c * INR (S n) * (y-t) ^ n)).
intros t Ht.
unfold g.
assert (Dp: forall n, derivable_pt_lim (fun x0 : R => (y - x0) ^ S n) t (INR (S n) * (y - t) ^ n * (0 - 1))).
intros m.
apply (derivable_pt_lim_comp (fun t => y - t) (fun t => t ^ (S m))).
apply derivable_pt_lim_minus.
apply derivable_pt_lim_const.
apply derivable_pt_lim_id.
apply derivable_pt_lim_pow.
apply: is_derive_plus.
clear c g.
rename n into N.
generalize (le_refl N).
generalize N at -2.
intros n Hn.
move: Hn.
induction n.
intros _.
simpl.
eapply filterdiff_ext_lin.
apply @filterdiff_minus_fct ; try by apply locally_filter.
apply filterdiff_const.
apply @filterdiff_scal_r_fct with (f := fun u => f u).
by apply locally_filter.
by apply Rmult_comm.
apply Derive_correct.
apply (Df t Ht 1%nat).
apply le_n_S.
apply le_0_n.
simpl => z.
rewrite /minus /plus /opp /zero /scal /= /mult /=.
field.
intros Hn.
apply filterdiff_ext with (fun x0 : R => (f y - (sum_f_R0 (fun m : nat => (y - x0) ^ m / INR (fact m) * Derive_n f m x0) n)) - (y - x0) ^ (S n) / INR (fact (S n)) * Derive_n f (S n) x0).
simpl.
intros; ring.
eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct ; try by apply locally_filter.
apply IHn.
now apply lt_le_weak.
apply @filterdiff_opp_fct ; try by apply locally_filter.
generalize (filterdiff_mult_fct (fun x0 => ((y - x0) ^ S n / INR (fact (S n)))) (fun x0 => Derive_n f (S n) x0)) => /= H.
apply H ; clear H.
by apply Rmult_comm.
apply @filterdiff_scal_l_fct ; try by apply locally_filter.
generalize (filterdiff_comp' (fun u => y - u) (fun x => pow x (S n))) => /= H ; apply H ; clear H.
apply @filterdiff_minus_fct ; try apply locally_filter.
apply filterdiff_const.
apply filterdiff_id.
apply is_derive_Reals.
apply (derivable_pt_lim_pow _ (S n)).
apply Derive_correct.
apply (Df t Ht (S (S n))).
now apply le_n_S.
move => z.
change (fact (S n)) with ((S n)*fact n)%nat.
rewrite mult_INR.
set v := INR (S n).
rewrite /minus /plus /opp /zero /scal /= /mult /=.
field.
split.
apply INR_fact_neq_0.
now apply not_0_INR.
eapply filterdiff_ext_lin.
apply filterdiff_ext with (fun x0 : R => -c * (y - x0) ^ S n).
simpl => z ; ring.
apply @filterdiff_scal_r_fct ; try by apply locally_filter.
by apply Rmult_comm.
apply is_derive_Reals, Dp.
set v := INR (S n).
simpl => z.
rewrite /scal /= /mult /=.
ring.
assert (Dg' : forall t : R, x <= t <= y -> derivable_pt g t).
intros t Ht.
exists (Derive g t).
apply is_derive_Reals.
apply Derive_correct.
eexists.
apply (Dg t Ht).
assert (pr : forall t : R, x < t < y -> derivable_pt g t).
intros t Ht.
apply Dg'.
split ; now apply Rlt_le.
assert (Zxy: (y - x) ^ (S n) <> 0).
apply pow_nonzero.
apply Rgt_not_eq.
apply Rplus_gt_reg_l with x.
now ring_simplify.
destruct (Rolle g x y pr) as (zeta, (Hzeta1,Hzeta2)).
intros t Ht.
apply derivable_continuous_pt.
now apply Dg'.
exact Hxy.
apply trans_eq with 0.
unfold g, c.
now field.
unfold g.
destruct n.
simpl; field.
rewrite decomp_sum.
rewrite sum_eq_R0.
simpl; field.
intros; simpl; field.
exact (INR_fact_neq_0 (S n0)).
apply lt_0_Sn.
exists zeta.
apply (conj Hzeta1).
rewrite Rmult_assoc.
replace (/ INR (fact (S n)) * Derive_n f (S n) zeta) with c.
unfold c.
now field.
apply Rmult_eq_reg_r with (INR (S n) * (y - zeta) ^ n).
apply Rplus_eq_reg_l with ((- (y - zeta) ^ n / INR (fact n) * Derive_n f (S n) zeta)).
change (fact (S n)) with (S n * fact n)%nat.
rewrite mult_INR.
apply trans_eq with 0.
rewrite -Rmult_assoc.
assert (H: x <= zeta <= y) by (split ; apply Rlt_le ; apply Hzeta1).
rewrite -(is_derive_unique _ _ _ (Dg _ H)).
destruct (pr zeta Hzeta1) as (x0,Hd).
simpl in Hzeta2.
rewrite Hzeta2 in Hd.
now apply is_derive_unique, is_derive_Reals.
field.
split.
apply INR_fact_neq_0.
now apply not_0_INR.
apply Rmult_integral_contrapositive_currified.
now apply not_0_INR.
apply pow_nonzero.
apply Rgt_not_eq.
apply Rplus_gt_reg_l with zeta.
ring_simplify.
apply Hzeta1.
