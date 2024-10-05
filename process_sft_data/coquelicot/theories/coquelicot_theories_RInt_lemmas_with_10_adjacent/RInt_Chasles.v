Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq SF_seq.
Require Import Continuity Hierarchy.
Section is_RInt.
Context {V : NormedModule R_AbsRing}.
Definition is_RInt (f : R -> V) (a b : R) (If : V) := filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd)) (Riemann_fine a b) (locally If).
Definition ex_RInt (f : R -> V) (a b : R) := exists If : V, is_RInt f a b If.
End is_RInt.
Section StepFun.
Context {V : NormedModule R_AbsRing}.
End StepFun.
Section norm_RInt.
Context {V : NormedModule R_AbsRing}.
End norm_RInt.
Section prod.
Context {U V : NormedModule R_AbsRing}.
End prod.
Section RInt.
Context {V : CompleteNormedModule R_AbsRing}.
Definition RInt (f : R -> V) (a b : R) := iota (is_RInt f a b).
End RInt.

Lemma ex_RInt_fct_extend_snd (f : R -> U * V) (a b : R) : ex_RInt f a b -> ex_RInt (fun t => snd (f t)) a b.
Proof.
intros [l Hl].
exists (snd l).
Admitted.

Lemma ex_RInt_fct_extend_pair (f : R -> U * V) (a b : R) : ex_RInt (fun t => fst (f t)) a b -> ex_RInt (fun t => snd (f t)) a b -> ex_RInt f a b.
Proof.
move => [l1 H1] [l2 H2].
exists (l1,l2).
Admitted.

Lemma RInt_fct_extend_pair (U_RInt : (R -> U) -> R -> R -> U) (V_RInt : (R -> V) -> R -> R -> V) : (forall f a b l, is_RInt f a b l -> U_RInt f a b = l) -> (forall f a b l, is_RInt f a b l -> V_RInt f a b = l) -> forall f a b l, is_RInt f a b l -> (U_RInt (fun t => fst (f t)) a b, V_RInt (fun t => snd (f t)) a b) = l.
Proof.
intros HU HV f a b l Hf.
apply injective_projections ; simpl.
apply HU ; by apply is_RInt_fct_extend_fst.
Admitted.

Lemma is_RInt_unique (f : R -> V) (a b : R) (l : V) : is_RInt f a b l -> RInt f a b = l.
Proof.
Admitted.

Lemma RInt_correct (f : R -> V) (a b : R) : ex_RInt f a b -> is_RInt f a b (RInt f a b).
Proof.
intros [If HIf].
Admitted.

Lemma opp_RInt_swap : forall f a b, ex_RInt f a b -> opp (RInt f a b) = RInt f b a.
Proof.
intros f a b [If HIf].
apply sym_eq, is_RInt_unique.
apply: is_RInt_swap.
apply RInt_correct.
Admitted.

Lemma RInt_ext (f g : R -> V) (a b : R) : (forall x, Rmin a b < x < Rmax a b -> f x = g x) -> RInt f a b = RInt g a b.
Proof.
intros Hfg.
apply eq_close.
apply: close_iota ; split ; apply is_RInt_ext.
exact Hfg.
intros t Ht.
Admitted.

Lemma RInt_point (a : R) (f : R -> V) : RInt f a a = zero.
Proof.
apply is_RInt_unique.
Admitted.

Lemma RInt_const (a b : R) (c : V) : RInt (fun _ => c) a b = scal (b - a) c.
Proof.
apply is_RInt_unique.
Admitted.

Lemma RInt_comp_lin (f : R -> V) (u v a b : R) : ex_RInt f (u * a + v) (u * b + v) -> RInt (fun y => scal u (f (u * y + v))) a b = RInt f (u * a + v) (u * b + v).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_comp_lin.
Admitted.

Lemma RInt_scal (f : R -> V) (a b l : R) : ex_RInt f a b -> RInt (fun x => scal l (f x)) a b = scal l (RInt f a b).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_scal.
Admitted.

Lemma RInt_opp (f : R -> V) (a b : R) : ex_RInt f a b -> RInt (fun x => opp (f x)) a b = opp (RInt f a b).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_opp.
Admitted.

Lemma RInt_plus : forall f g a b, ex_RInt f a b -> ex_RInt g a b -> RInt (fun x => plus (f x) (g x)) a b = plus (RInt f a b) (RInt g a b).
Proof.
intros f g a b Hf Hg.
apply is_RInt_unique.
Admitted.

Lemma RInt_minus : forall f g a b, ex_RInt f a b -> ex_RInt g a b -> RInt (fun x => minus (f x) (g x)) a b = minus (RInt f a b) (RInt g a b).
Proof.
intros f g a b Hf Hg.
apply is_RInt_unique.
Admitted.

Lemma is_RInt_ge_0 (f : R -> R) (a b If : R) : a <= b -> is_RInt f a b If -> (forall x, a < x < b -> 0 <= f x) -> 0 <= If.
Proof.
intros Hab HIf Hf.
set (f' := fun x => if Rle_dec x a then 0 else if Rle_dec b x then 0 else f x).
apply is_RInt_ext with (g := f') in HIf.
apply closed_filterlim_loc with (1 := HIf) (3 := closed_ge 0).
unfold Riemann_fine, within.
apply filter_forall.
intros ptd Hptd.
replace 0 with (scal (sign (b - a)) (Riemann_sum (fun _ => 0) ptd)).
apply Rmult_le_compat_l.
apply sign_ge_0.
now apply Rge_le, Rge_minus, Rle_ge.
apply Riemann_sum_le.
apply Hptd.
intros t _.
unfold f'.
case Rle_dec as [H1|H1].
apply Rle_refl.
case Rle_dec as [H2|H2].
apply Rle_refl.
apply Hf.
now split; apply Rnot_le_lt.
rewrite Riemann_sum_const.
by rewrite !scal_zero_r.
rewrite (Rmin_left _ _ Hab) (Rmax_right _ _ Hab).
intros x Hx.
unfold f'.
case Rle_dec as [H1|H1].
now elim (Rle_not_lt _ _ H1).
case Rle_dec as [H2|H2].
now elim (Rle_not_lt _ _ H2).
Admitted.

Lemma RInt_ge_0 (f : R -> R) (a b : R) : a <= b -> ex_RInt f a b -> (forall x, a < x < b -> 0 <= f x) -> 0 <= RInt f a b.
Proof.
intros Hab Hf Hpos.
apply: is_RInt_ge_0 Hab _ Hpos.
Admitted.

Lemma is_RInt_le (f g : R -> R) (a b If Ig : R) : a <= b -> is_RInt f a b If -> is_RInt g a b Ig -> (forall x, a < x < b -> f x <= g x) -> If <= Ig.
Proof.
intros Hab Hf Hg Hfg.
apply Rminus_le_0.
apply: is_RInt_ge_0 Hab _ _.
apply: is_RInt_minus Hg Hf.
intros x Hx.
apply -> Rminus_le_0.
Admitted.

Lemma RInt_le (f g : R -> R) (a b : R) : a <= b -> ex_RInt f a b -> ex_RInt g a b-> (forall x, a < x < b -> f x <= g x) -> RInt f a b <= RInt g a b.
Proof.
intros Hab Hf Hg Hfg.
apply: is_RInt_le Hab _ _ Hfg.
exact: RInt_correct.
Admitted.

Lemma RInt_gt_0 (g : R -> R) (a b : R) : (a < b) -> (forall x, a < x < b -> (0 < g x)) -> (forall x, a <= x <= b -> continuous g x) -> 0 < RInt g a b.
Proof.
intros Hab Hg Cg.
set c := (a + b) / 2.
assert (Hc : a < c < b).
unfold c ; lra.
assert (H : locally c (fun (x : R) => g c / 2 <= g x)).
specialize (Hg _ Hc).
specialize (Cg c (conj (Rlt_le _ _ (proj1 Hc)) (Rlt_le _ _ (proj2 Hc)))).
case: (proj1 (filterlim_locally _ _) Cg (pos_div_2 (mkposreal _ Hg))) => /= d Hd.
exists d => /= x Hx.
specialize (Hd _ Hx).
rewrite /ball /= /AbsRing_ball in Hd.
apply Rabs_lt_between' in Hd.
field_simplify (g c - g c / 2) in Hd.
by apply Rlt_le, Hd.
assert (Ig : ex_RInt g a b).
apply @ex_RInt_continuous.
rewrite Rmin_left.
rewrite Rmax_right.
intros.
now apply Cg.
by apply Rlt_le.
by apply Rlt_le.
case: H => /= d Hd.
set a' := Rmax (c - d / 2) ((a + c) / 2).
set b' := Rmin (c + d / 2) ((c + b) / 2).
assert (Hab' : a' < b').
apply Rlt_trans with c.
apply Rmax_case.
generalize (cond_pos d) ; lra.
lra.
apply Rmin_case.
generalize (cond_pos d) ; lra.
lra.
assert (Ha' : a < a' < b).
split.
eapply Rlt_le_trans, Rmax_r.
lra.
apply Rmax_case.
generalize (cond_pos d) ; lra.
lra.
assert (Hb' : a < b' < b).
split.
lra.
eapply Rle_lt_trans.
apply Rmin_r.
lra.
assert (ex_RInt g a a').
eapply @ex_RInt_Chasles_1, Ig ; split ; by apply Rlt_le, Ha'.
assert (ex_RInt g a' b).
eapply @ex_RInt_Chasles_2, Ig ; split ; by apply Rlt_le, Ha'.
assert (ex_RInt g a' b').
eapply @ex_RInt_Chasles_1, H0 ; split => // ; apply Rlt_le => //.
by apply Hb'.
assert (ex_RInt g b' b).
eapply @ex_RInt_Chasles_2, H0 ; split => // ; apply Rlt_le => //.
by apply Hb'.
rewrite -(RInt_Chasles g a a' b) //.
apply Rplus_le_lt_0_compat.
apply (is_RInt_ge_0 g a a').
by apply Rlt_le, Ha'.
exact: RInt_correct.
intros ; apply Rlt_le, Hg ; split.
by apply H3.
eapply Rlt_trans, Ha'.
apply H3.
rewrite -(RInt_Chasles g a' b' b) //.
apply Rplus_lt_le_0_compat.
apply Rlt_le_trans with ((b' - a') * (g c / 2)).
specialize (Hg _ Hc).
apply Rmult_lt_0_compat.
by apply -> Rminus_lt_0.
apply Rdiv_lt_0_compat => //.
by apply Rlt_0_2.
eapply is_RInt_le.
apply Rlt_le, Hab'.
apply @is_RInt_const.
exact: RInt_correct.
intros ; apply Hd.
rewrite (double_var d).
apply Rabs_lt_between' ; split.
eapply Rlt_trans, H3.
eapply Rlt_le_trans, Rmax_l.
apply Rminus_lt_0 ; ring_simplify.
by apply is_pos_div_2.
eapply Rlt_trans.
apply H3.
eapply Rle_lt_trans.
apply Rmin_l.
apply Rminus_lt_0 ; ring_simplify.
by apply is_pos_div_2.
eapply is_RInt_ge_0.
2: exact: RInt_correct.
apply Rlt_le, Hb'.
intros ; apply Rlt_le, Hg.
split.
eapply Rlt_trans, H3.
by apply Hb'.
Admitted.

Lemma RInt_lt (f g : R -> R) (a b : R) : a < b -> (forall x : R, a <= x <= b ->continuous g x) -> (forall x : R, a <= x <= b ->continuous f x) -> (forall x : R, a < x < b -> f x < g x) -> RInt f a b < RInt g a b.
Proof.
intros Hab Cg Cf Hfg.
apply Rminus_lt_0.
assert (Ig : ex_RInt g a b).
apply @ex_RInt_continuous.
rewrite Rmin_left.
rewrite Rmax_right.
intros.
now apply Cg.
by apply Rlt_le.
by apply Rlt_le.
assert (ex_RInt f a b).
apply @ex_RInt_continuous.
rewrite Rmin_left.
rewrite Rmax_right.
intros.
now apply Cf.
by apply Rlt_le.
by apply Rlt_le.
rewrite -[Rminus]/(@minus R_AbelianGroup) -RInt_minus //.
apply RInt_gt_0 => //.
now intros ; apply -> Rminus_lt_0 ; apply Hfg.
intros.
apply @continuous_minus.
by apply Cg.
Admitted.

Lemma RInt_Chasles : forall f a b c, ex_RInt f a b -> ex_RInt f b c -> plus (RInt f a b) (RInt f b c) = RInt f a c.
Proof.
intros f a b c H1 H2.
apply sym_eq, is_RInt_unique.
apply: is_RInt_Chasles ; now apply RInt_correct.
