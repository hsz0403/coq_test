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

Lemma continuity_2d_pt_ext_loc : forall f g x y, locally_2d (fun u v => f u v = g u v) x y -> continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq Cf.
apply locally_2d_locally in Heq.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim.
rewrite -(locally_singleton _ _ Heq).
apply filterlim_ext_loc with (2 := Cf).
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

Lemma continuous_ext : forall (f g : T -> U) (x : T), (forall x, f x = g x) -> continuous f x -> continuous g x.
Proof.
intros f g x H Cf.
apply filterlim_ext with (1 := H).
Admitted.

Lemma continuous_on_ext : forall (D : T -> Prop) (f g : T -> U), (forall x, D x -> f x = g x) -> continuous_on D f -> continuous_on D g.
Proof.
intros D f g H Cf x Dx.
apply filterlim_within_ext with (1 := H).
rewrite <- H with (1 := Dx).
Admitted.

Lemma continuous_comp {U V W : UniformSpace} (f : U -> V) (g : V -> W) (x : U) : continuous f x -> continuous g (f x) -> continuous (fun x => g (f x)) x.
Proof.
Admitted.

Lemma continuous_comp_2 {U V W X : UniformSpace} (f : U -> V) (g : U -> W) (h : V -> W -> X) (x : U) : continuous f x -> continuous g x -> continuous (fun (x : V * W) => h (fst x) (snd x)) (f x,g x) -> continuous (fun x => h (f x) (g x)) x.
Proof.
intros Cf Cg Ch.
eapply filterlim_comp_2.
by apply Cf.
by apply Cg.
apply filterlim_locally => eps.
case: (proj1 (filterlim_locally _ _) Ch eps) => /= del Hdel.
rewrite {1}/ball /= /prod_ball /= in Hdel.
exists (fun y => ball (f x) (pos del) y) (fun y => ball (g x) (pos del) y).
apply locally_ball.
apply locally_ball.
move => y z /= Hy Hz.
apply (Hdel (y,z)).
Admitted.

Lemma is_lim_comp_continuous (f g : R -> R) (x : Rbar) (l : R) : is_lim f x l -> continuous g l -> is_lim (fun x => g (f x)) x (g l).
Proof.
intros Hf Hg.
apply filterlim_locally => eps.
destruct (proj1 (filterlim_locally _ _) Hg eps) as [e He] ; clear Hg.
eapply filter_imp.
intros y Hy.
apply He, Hy.
Admitted.

Lemma continuous_fst {U V : UniformSpace} (x : U) (y : V) : continuous (fst (B:=V)) (x, y).
Proof.
intros P [d Hd].
exists d => z [/= Hz1 Hz2].
Admitted.

Lemma continuous_snd {U V : UniformSpace} (x : U) (y : V) : continuous (snd (B:=V)) (x, y).
Proof.
intros P [d Hd].
exists d => z [/= Hz1 Hz2].
Admitted.

Lemma continuous_const {U V : UniformSpace} (c : V) (x : U) : continuous (fun _ => c) x.
Proof.
Admitted.

Lemma continuous_id {U : UniformSpace} (x : U) : continuous (fun y => y) x.
Proof.
Admitted.

Lemma continuous_opp (f : U -> V) (x : U) : continuous f x -> continuous (fun x : U => opp (f x)) x.
Proof.
intros.
eapply filterlim_comp.
by apply H.
Admitted.

Lemma continuous_plus (f g : U -> V) (x : U) : continuous f x -> continuous g x -> continuous (fun x : U => plus (f x) (g x)) x.
Proof.
intros.
eapply filterlim_comp_2.
by apply H.
by apply H0.
Admitted.

Lemma continuous_minus (f g : U -> V) (x : U) : continuous f x -> continuous g x -> continuous (fun x : U => minus (f x) (g x)) x.
Proof.
intros.
apply continuous_plus.
apply H.
Admitted.

Lemma continuous_scal (k : U -> K) (f : U -> V) (x : U) : continuous k x -> continuous f x -> continuous (fun y => scal (k y) (f y)) x.
Proof.
intros.
Admitted.

Lemma continuous_scal_r (k : K) (f : U -> V) (x : U) : continuous f x -> continuous (fun y => scal k (f y)) x.
Proof.
intros.
Admitted.

Lemma continuous_scal_l (f : U -> K) (k : V) (x : U) : continuous f x -> continuous (fun y => scal (f y) k) x.
Proof.
intros.
apply (continuous_comp f (fun y => scal y k)) => //.
Admitted.

Lemma continuous_mult {U : UniformSpace} {K : AbsRing} (f g : U -> K) (x : U) : continuous f x -> continuous g x -> continuous (fun y => mult (f y) (g y)) x.
Proof.
intros.
Admitted.

Lemma unifcont_1d (f : R -> V) a b : (forall x, a <= x <= b -> continuous f x) -> forall eps : posreal, {delta : posreal | forall x y, a <= x <= b -> a <= y <= b -> ball x delta y -> ~~ ball (f x) eps (f y)}.
Proof.
intros Cf eps.
wlog: f Cf / (forall z : R, continuous f z) => [ Hw | {Cf} Cf ].
destruct (C0_extension_le f a b) as [g [Cg Hg]].
by apply Cf.
destruct (Hw g) as [d Hd].
intros x Hx ; apply Cg.
apply Cg.
exists d => x y Hx Hy Hxy.
rewrite -!Hg //.
by apply Hd.
assert (forall (x : R), {delta : posreal | forall y : R, ball x delta y -> ~~ ball (f x) (pos_div_2 eps) (f y)}).
move: (pos_div_2 eps) => {eps} eps x.
assert (Rbar_lt 0 (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y)))).
case: (Lub.Lub_Rbar_correct (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))).
move: (Lub.Lub_Rbar _) => l H1 H2.
case: (proj1 (filterlim_locally _ _) (Cf x) eps) => d Hd.
eapply Rbar_lt_le_trans, H1.
by apply d.
by apply Hd.
assert (0 < Rbar_min 1 (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y)))).
move: H ; case: (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))) => [l | | ] //= H0.
apply Rmin_case => //.
by apply Rlt_0_1.
by apply Rlt_0_1.
set d := mkposreal _ H0.
exists d.
unfold d ; clear d ; simpl.
case: (Lub.Lub_Rbar_correct (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))).
move: (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))) H => {H0} l H0 H1 H2 y Hy.
contradict Hy.
apply Rle_not_lt.
apply (Rbar_le_trans (Finite _) l (Finite _)).
case: (l) H0 => [r | | ] //= H0.
apply Rmin_r.
apply H2 => d /= Hd.
apply Rnot_lt_le ; contradict Hy.
by apply Hd.
destruct (compactness_value_1d a b (fun x => pos_div_2 (proj1_sig (H x)))) as [d Hd].
exists d => x y Hx Hy Hxy Hf.
apply (Hd x Hx).
case => {Hd} t [Ht].
case: H => /= delta Hdelta [Htx Hdt].
apply (Hdelta x).
eapply ball_le, Htx.
rewrite {2}(double_var delta).
apply Rminus_le_0 ; ring_simplify.
apply Rlt_le, is_pos_div_2.
intro Hftx.
apply (Hdelta y).
rewrite (double_var delta).
apply ball_triangle with x.
apply Htx.
by eapply ball_le, Hxy.
contradict Hf.
rewrite (double_var eps).
eapply ball_triangle, Hf.
Admitted.

Lemma unifcont_normed_1d (f : R -> V) a b : (forall x, a <= x <= b -> continuous f x) -> forall eps : posreal, {delta : posreal | forall x y, a <= x <= b -> a <= y <= b -> ball x delta y -> ball_norm (f x) eps (f y)}.
Proof.
intros H eps.
assert (0 < eps / (@norm_factor _ V)).
apply Rdiv_lt_0_compat.
apply cond_pos.
exact norm_factor_gt_0.
destruct (unifcont_1d f a b H (mkposreal _ H0)) as [d Hd].
exists d => x y Hx Hy Hxy.
specialize (Hd x y Hx Hy Hxy).
apply Rnot_le_lt.
contradict Hd ; contradict Hd.
apply Rlt_not_le.
evar_last.
apply norm_compat2, Hd.
simpl ; field.
Admitted.

Lemma continuous_ext_loc (f g : T -> U) (x : T) : locally x (fun y : T => g y = f y) -> continuous g x -> continuous f x.
Proof.
intros.
eapply filterlim_ext_loc.
by apply H.
by rewrite -(locally_singleton _ _ H).
