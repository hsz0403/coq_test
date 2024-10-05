Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Compactness Lim_seq.
Definition is_lim (f : R -> R) (x l : Rbar) := filterlim f (Rbar_locally' x) (Rbar_locally l).
Definition is_lim' (f : R -> R) (x l : Rbar) := match l with | Finite l => forall eps : posreal, Rbar_locally' x (fun y => Rabs (f y - l) < eps) | p_infty => forall M : R, Rbar_locally' x (fun y => M < f y) | m_infty => forall M : R, Rbar_locally' x (fun y => f y < M) end.
Definition ex_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_lim f x l.
Definition ex_finite_lim (f : R -> R) (x : Rbar) := exists l : R, is_lim f x l.
Definition Lim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).
Definition continuity_2d_pt f x y := forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.
Section Continuity.
Context {T U : UniformSpace}.
Definition continuous_on (D : T -> Prop) (f : T -> U) := forall x, D x -> filterlim f (within D (locally x)) (locally (f x)).
Definition continuous (f : T -> U) (x : T) := filterlim f (locally x) (locally (f x)).
End Continuity.
Section Continuity_op.
Context {U : UniformSpace} {K : AbsRing} {V : NormedModule K}.
End Continuity_op.
Section UnifCont.
Context {V : UniformSpace}.
End UnifCont.
Section UnifCont_N.
Context {K : AbsRing} {V : NormedModule K}.
End UnifCont_N.

Lemma uniform_continuity_2d : forall f a b c d, (forall x y, a <= x <= b -> c <= y <= d -> continuity_2d_pt f x y) -> forall eps : posreal, exists delta : posreal, forall x y u v, a <= x <= b -> c <= y <= d -> a <= u <= b -> c <= v <= d -> Rabs (u - x) < delta -> Rabs (v - y) < delta -> Rabs (f u v - f x y) < eps.
Proof.
intros f a b c d Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x y Hx Hy => locally_2d_ex_dec (P x y) x y _ (Cf x y Hx Hy _))).
intros delta1.
set (delta2 x y := match Rle_dec a x, Rle_dec x b, Rle_dec c y, Rle_dec y d with left Ha, left Hb, left Hc, left Hd => pos_div_2 (proj1_sig (delta1 x y (conj Ha Hb) (conj Hc Hd))) | _, _, _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_2d a b c d delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux Hvy.
specialize (Hdelta x y Hx Hy).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&q&(Hap,Hpb)&(Hcq,Hqd)&Hxp&Hyq&Hd).
replace (f u v - f x y) with (f u v - f p q + (f p q - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hyq Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
case Rle_dec => Hcq' ; try easy.
case Rle_dec => Hqd' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hyq Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
replace (v - q) with (v - y + (y - q)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hyq).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hvy).
apply: Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_trans with (1 := Hyq).
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
Admitted.

Lemma uniform_continuity_2d_1d : forall f a b c, (forall x, a <= x <= b -> continuity_2d_pt f x c) -> forall eps : posreal, exists delta : posreal, forall x y u v, a <= x <= b -> c - delta <= y <= c + delta -> a <= u <= b -> c - delta <= v <= c + delta -> Rabs (u - x) < delta -> Rabs (f u v - f x y) < eps.
Proof.
intros f a b c Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x Hx => locally_2d_ex_dec (P x c) x c _ (Cf x Hx _))).
intros delta1.
set (delta2 x := match Rle_dec a x, Rle_dec x b with left Ha, left Hb => pos_div_2 (proj1_sig (delta1 x (conj Ha Hb))) | _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_1d a b delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux.
specialize (Hdelta x Hx).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&(Hap,Hpb)&Hxp&Hd).
replace (f u v - f x y) with (f u v - f p c + (f p c - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
Admitted.

Lemma uniform_continuity_2d_1d' : forall f a b c, (forall x, a <= x <= b -> continuity_2d_pt f c x) -> forall eps : posreal, exists delta : posreal, forall x y u v, a <= x <= b -> c - delta <= y <= c + delta -> a <= u <= b -> c - delta <= v <= c + delta -> Rabs (u - x) < delta -> Rabs (f v u - f y x) < eps.
Proof.
intros f a b c Cf eps.
assert (T:(forall x : R, a <= x <= b -> continuity_2d_pt (fun x0 y : R => f y x0) x c) ).
intros x Hx e.
destruct (Cf x Hx e) as (d,Hd).
exists d.
intros; now apply Hd.
destruct (uniform_continuity_2d_1d (fun x y => f y x) a b c T eps) as (d,Hd).
exists d; intros.
Admitted.

Lemma continuity_2d_pt_neq_0 : forall f x y, continuity_2d_pt f x y -> f x y <> 0 -> locally_2d (fun u v => f u v <> 0) x y.
Proof.
intros f x y Cf H.
apply continuity_2d_pt_filterlim in Cf.
apply locally_2d_locally.
apply (Cf (fun y => y <> 0)).
Admitted.

Lemma continuity_pt_id : forall x, continuity_pt (fun x => x) x.
Proof.
intros x.
apply continuity_pt_filterlim.
Admitted.

Lemma continuity_2d_pt_id1 : forall x y, continuity_2d_pt (fun u v => u) x y.
Proof.
Admitted.

Lemma continuity_2d_pt_id2 : forall x y, continuity_2d_pt (fun u v => v) x y.
Proof.
Admitted.

Lemma continuity_2d_pt_const : forall x y c, continuity_2d_pt (fun u v => c) x y.
Proof.
intros x y c eps; exists eps; rewrite Rminus_eq_0 Rabs_R0.
Admitted.

Lemma continuity_pt_ext_loc : forall f g x, locally x (fun x => f x = g x) -> continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq Cf.
apply continuity_pt_filterlim in Cf.
apply continuity_pt_filterlim.
rewrite -(locally_singleton _ _ Heq).
Admitted.

Lemma continuity_pt_ext : forall f g x, (forall x, f x = g x) -> continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq.
apply continuity_pt_ext_loc.
Admitted.

Lemma continuity_2d_pt_ext : forall f g x y, (forall x y, f x y = g x y) -> continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq.
apply continuity_2d_pt_ext_loc.
apply locally_2d_locally.
apply filter_forall.
Admitted.

Lemma continuity_1d_2d_pt_comp : forall f g x y, continuity_pt f (g x y) -> continuity_2d_pt g x y -> continuity_2d_pt (fun x y => f (g x y)) x y.
Proof.
intros f g x y Cf Cg.
apply continuity_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
Admitted.

Lemma continuity_2d_pt_opp (f : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt (fun u v => - f u v) x y.
Proof.
apply continuity_1d_2d_pt_comp.
apply continuity_pt_opp.
Admitted.

Lemma continuity_2d_pt_plus (f g : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt g x y -> continuity_2d_pt (fun u v => f u v + g u v) x y.
Proof.
intros Cf Cg.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
eapply filterlim_comp_2.
apply Cf.
apply Cg.
Admitted.

Lemma continuity_2d_pt_minus (f g : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt g x y -> continuity_2d_pt (fun u v => f u v - g u v) x y.
Proof.
move => Cf Cg.
apply continuity_2d_pt_plus.
exact: Cf.
Admitted.

Lemma continuity_2d_pt_inv (f : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> f x y <> 0 -> continuity_2d_pt (fun u v => / f u v) x y.
Proof.
intros Cf Df.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim.
apply filterlim_comp with (1 := Cf).
apply (filterlim_Rbar_inv (f x y)).
contradict Df.
Admitted.

Lemma continuity_2d_pt_mult (f g : R -> R -> R) (x y : R) : continuity_2d_pt f x y -> continuity_2d_pt g x y -> continuity_2d_pt (fun u v => f u v * g u v) x y.
Proof.
intros Cf Cg.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
eapply filterlim_comp_2.
apply Cf.
apply Cg.
Admitted.

Lemma continuous_continuous_on : forall (D : T -> Prop) (f : T -> U) (x : T), locally x D -> continuous_on D f -> continuous f x.
Proof.
intros D f x Dx CD P Pfx.
assert (Dx' := locally_singleton _ _ Dx).
generalize (filter_and _ _ Dx (CD x Dx' P Pfx)).
unfold filtermap, within.
apply filter_imp.
intros t [H1 H2].
Admitted.

Lemma continuous_on_subset : forall (D E : T -> Prop) (f : T -> U), (forall x, E x -> D x) -> continuous_on D f -> continuous_on E f.
Proof.
intros D E f H CD x Ex P Pfx.
generalize (CD x (H x Ex) P Pfx).
unfold filtermap, within.
apply filter_imp.
intros t H' Et.
Admitted.

Lemma continuous_on_forall : forall (D : T -> Prop) (f : T -> U), (forall x, D x -> continuous f x) -> continuous_on D f.
Proof.
intros D f H x Dx P Pfx.
generalize (H x Dx P Pfx).
unfold filtermap, within.
Admitted.

Lemma continuity_2d_pt_ext_loc : forall f g x y, locally_2d (fun u v => f u v = g u v) x y -> continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq Cf.
apply locally_2d_locally in Heq.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim.
rewrite -(locally_singleton _ _ Heq).
apply filterlim_ext_loc with (2 := Cf).
by apply Heq.
