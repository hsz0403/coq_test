Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Hierarchy Seq_fct RInt PSeries.
Section Continuity.
Context {V : NormedModule R_AbsRing}.
End Continuity.
Section Derive.
Context {V : NormedModule R_AbsRing}.
End Derive.
Section Derive'.
Context {V : CompleteNormedModule R_AbsRing}.
End Derive'.
Section Comp.
Context {V : CompleteNormedModule R_AbsRing}.
End Comp.
Section RInt_comp.
Context {V : NormedModule R_AbsRing}.
End RInt_comp.
Definition PS_Int (a : nat -> R) (n : nat) : R := match n with | O => 0 | S n => a n / INR (S n) end.
Section ByParts.
Context {V : CompleteNormedModule R_AbsRing}.
End ByParts.

Lemma is_RInt_comp (f : R -> V) (g dg : R -> R) (a b : R) : (forall x, Rmin a b <= x <= Rmax a b -> continuous f (g x)) -> (forall x, Rmin a b <= x <= Rmax a b -> is_derive g x (dg x) /\ continuous dg x) -> is_RInt (fun y => scal (dg y) (f (g y))) a b (RInt f (g a) (g b)).
Proof.
wlog: a b / (a < b) => [Hw|Hab].
case: (total_order_T a b) => [[Hab'|Hab']|Hab'] Hf Hg.
-
exact: Hw.
-
rewrite Hab'.
by rewrite RInt_point; apply: is_RInt_point.
-
rewrite <- (opp_opp (RInt f _ _)).
apply: is_RInt_swap.
rewrite opp_RInt_swap.
apply Hw => // .
by rewrite Rmin_comm Rmax_comm.
by rewrite Rmin_comm Rmax_comm.
apply: ex_RInt_continuous => z Hz.
case: (IVT_gen_consistent (extension_C0 g b a) b a z).
+
apply: extension_C0_continuous => /=; try lra.
move => x Hbx Hxa; apply: ex_derive_continuous.
by exists (dg x); apply Hg; rewrite Rmin_right ?Rmax_left; try lra.
+
rewrite !(extension_C0_ext) /=; try lra.
by rewrite Rmin_comm Rmax_comm.
+
move => x [Hx1 Hx2].
rewrite -Hx2.
rewrite Rmin_left ?Rmax_right in Hx1; try lra.
rewrite (extension_C0_ext) /=; try lra.
apply: Hf.
by move: Hx1; rewrite Rmin_right ?Rmax_left; lra.
rewrite -> Rmin_left by now apply Rlt_le.
rewrite -> Rmax_right by now apply Rlt_le.
wlog: g dg / (forall x : R, is_derive g x (dg x) /\ continuous dg x) => [Hw Hf Hg | Hg Hf _].
rewrite -?(extension_C1_ext g dg a b) ; try by [left | right].
set g0 := extension_C1 g dg a b.
set dg0 := extension_C0 dg a b.
apply is_RInt_ext with (fun y : R => scal (dg0 y) (f (g0 y))).
+
rewrite /Rmin /Rmax /g0 ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hx.
apply f_equal2.
by apply extension_C0_ext ; by apply Rlt_le, Hx.
by apply f_equal, extension_C1_ext ; by apply Rlt_le, Hx.
+
apply Hw.
*
intros x ; split.
apply extension_C1_is_derive.
by apply Rlt_le.
by intros ; apply Hg ; by split.
*
apply @extension_C0_continuous.
by apply Rlt_le.
intros ; apply Hg ; by split.
*
intros ; rewrite /g0 extension_C1_ext.
by apply Hf.
by apply H.
by apply H.
intros ; split.
apply extension_C1_is_derive.
by apply Rlt_le.
intros ; apply Hg ; by split.
apply @extension_C0_continuous.
by apply Rlt_le.
by intros ; apply Hg ; by split.
have cg : forall x, continuous g x.
move => t Ht; apply: ex_derive_continuous.
by exists (dg t); apply Hg.
wlog: f Hf / (forall x, continuous f x) => [Hw | {Hf} Hf].
case: (continuous_ab_maj_consistent g a b (Rlt_le _ _ Hab)) => [ | M HM].
move => x Hx; apply: ex_derive_continuous.
by exists (dg x); apply Hg.
case: (continuous_ab_min_consistent g a b (Rlt_le _ _ Hab)) => [ | m Hm].
move => x Hx; apply: ex_derive_continuous.
by exists (dg x) ; apply Hg.
have H : g m <= g M.
by apply Hm ; intuition.
case: (C0_extension_le f (g m) (g M)) => [ y Hy | f0 Hf0].
+
case: (IVT_gen_consistent g m M y) => // .
rewrite /Rmin /Rmax ; case: Rle_dec => // .
move => x [Hx <-].
apply Hf ; split.
apply Rle_trans with (2 := proj1 Hx).
by apply Rmin_case ; intuition.
apply Rle_trans with (1 := proj2 Hx).
apply Rmax_case ; intuition.
apply is_RInt_ext with (fun y : R => scal (dg y) (f0 (g y))).
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x Hc.
apply f_equal.
apply Hf0 ; split.
by apply Hm ; split ; apply Rlt_le ; apply Hc.
by apply HM ; split ; apply Rlt_le ; apply Hc.
rewrite -(RInt_ext f0).
+
apply Hw.
by move => x Hx ; apply Hf0.
by move => x ; apply Hf0.
+
move => x Hx.
case: (IVT_gen_consistent g a b x cg) => // .
by lra.
rewrite Rmin_left ?Rmax_right; try lra.
move => x0 Hx0.
case: Hx0 => Hx0 Hgx0x; rewrite -Hgx0x.
apply Hf0; split.
by apply Hm.
by apply HM.
evar_last.
+
apply (is_RInt_derive (fun x => RInt f (g a) (g x))).
move => x Hx.
evar_last.
apply is_derive_comp.
apply is_derive_RInt with (g a).
apply filter_forall => y.
apply RInt_correct, @ex_RInt_continuous.
by intros ; apply Hf.
by apply Hf.
by apply Hg.
reflexivity.
intros x Hx.
apply: @continuous_scal.
by apply Hg.
apply continuous_comp.
apply @ex_derive_continuous.
by eexists ; apply Hg.
by apply Hf.
+
by rewrite RInt_point minus_zero_r.
