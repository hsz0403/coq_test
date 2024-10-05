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

Lemma is_RInt_derive (f df : R -> V) (a b : R) : (forall x : R, Rmin a b <= x <= Rmax a b -> is_derive f x (df x)) -> (forall x : R, Rmin a b <= x <= Rmax a b -> continuous df x) -> is_RInt df a b (minus (f b) (f a)).
Proof.
intros Hf Hdf.
wlog Hab: a b Hf Hdf / (a < b).
intros H.
destruct (Rlt_or_le a b) as [Hab|Hab].
exact: H.
destruct Hab as [Hab|Hab].
+
rewrite -(opp_opp (minus _ _)).
apply: is_RInt_swap.
rewrite opp_minus.
apply H.
by rewrite Rmin_comm Rmax_comm.
by rewrite Rmin_comm Rmax_comm.
easy.
+
rewrite Hab.
rewrite /minus plus_opp_r.
by apply: is_RInt_point.
rewrite Rmin_left in Hf; last by lra.
rewrite Rmax_right in Hf; last by lra.
rewrite Rmin_left in Hdf; last by lra.
rewrite Rmax_right in Hdf; last by lra.
have Hminab : Rmin a b = a by rewrite Rmin_left; lra.
have Hmaxab : Rmax a b = b by rewrite Rmax_right; lra.
evar_last.
apply RInt_correct.
apply (ex_RInt_continuous df) => t Ht.
rewrite Hminab Hmaxab in Ht.
exact:Hdf.
apply (plus_reg_r (opp (f b))).
rewrite /minus -plus_assoc (plus_comm (opp _)) plus_assoc plus_opp_r.
rewrite -(RInt_point a df).
apply: sym_eq.
have Hext : forall x : R, Rmin a b < x < Rmax a b -> extension_C0 df a b x = df x.
move => x; rewrite Hminab Hmaxab => Hx.
by rewrite extension_C0_ext //=; lra.
rewrite -(RInt_ext _ _ _ _ Hext).
rewrite RInt_point -(RInt_point a (extension_C0 df a b)).
rewrite -!(extension_C1_ext f df a b) /=; try lra.
apply: (eq_is_derive (fun t => minus (RInt _ a t) (_ t))) => // t Ht.
have -> : zero = minus (extension_C0 df a b t) (extension_C0 df a b t) by rewrite minus_eq_zero.
apply: is_derive_minus; last first.
apply: extension_C1_is_derive => /=; first by lra.
by move => x Hax Hxb; apply: Hf; lra.
apply: (is_derive_RInt _ _ a).
apply: filter_forall.
move => x; apply: RInt_correct.
apply: ex_RInt_continuous.
move => z Hz; apply: extension_C0_continuous => /=; try lra.
by move => x0 Hax0 Hx0b; apply: Hdf; lra.
apply: extension_C0_continuous => /=; try lra.
move => x0 Hax0 Hx0b; apply: Hdf; lra.
