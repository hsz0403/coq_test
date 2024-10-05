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

Lemma is_derive_RInt_0 (f If : R -> V) (a : R) : locally a (fun b => is_RInt f a b (If b)) -> continuous f a -> is_derive If a (f a).
Proof.
intros HIf Hf.
split ; simpl.
apply is_linear_scal_l.
intros y Hy.
apply @is_filter_lim_locally_unique in Hy.
rewrite -Hy {y Hy}.
intros eps.
generalize (proj1 (filterlim_locally _ _) Hf) => {Hf} Hf.
eapply filter_imp.
simpl ; intros y Hy.
replace (If a) with (@zero V).
rewrite @minus_zero_r.
rewrite Rmult_comm ; eapply norm_RInt_le_const_abs ; last first.
apply is_RInt_minus.
instantiate (1 := f).
eapply (proj1 Hy).
apply is_RInt_const.
simpl.
apply (proj2 Hy).
apply locally_singleton in HIf.
set (HIf_0 := is_RInt_point f a).
apply (filterlim_locally_unique _ _ _ HIf_0 HIf).
apply filter_and.
by apply HIf.
assert (0 < eps / @norm_factor _ V).
apply Rdiv_lt_0_compat.
by apply eps.
by apply norm_factor_gt_0.
case: (Hf (mkposreal _ H)) => {Hf} delta Hf.
exists delta ; intros y Hy z Hz.
eapply Rle_trans.
apply Rlt_le, norm_compat2.
apply Hf.
apply Rabs_lt_between'.
move/Rabs_lt_between': Hy => Hy.
rewrite /Rmin /Rmax in Hz ; destruct (Rle_dec a y) as [Hxy | Hxy].
split.
eapply Rlt_le_trans, Hz.
apply Rminus_lt_0 ; ring_simplify.
by apply delta.
eapply Rle_lt_trans, Hy.
by apply Hz.
split.
eapply Rlt_le_trans, Hz.
by apply Hy.
eapply Rle_lt_trans.
apply Hz.
apply Rminus_lt_0 ; ring_simplify.
by apply delta.
simpl ; apply Req_le.
field.
apply Rgt_not_eq, norm_factor_gt_0.
