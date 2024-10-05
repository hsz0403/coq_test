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

Lemma is_lim_div (f g : R -> R) (x lf lg : Rbar) : is_lim f x lf -> is_lim g x lg -> lg <> 0 -> ex_Rbar_div lf lg -> is_lim (fun y => f y / g y) x (Rbar_div lf lg).
Proof.
move => Hf Hg Hlg Hl.
apply is_lim_mult ; try assumption.
Admitted.

Lemma ex_lim_div (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> Lim g x <> 0 -> ex_Rbar_div (Lim f x) (Lim g x) -> ex_lim (fun y => f y / g y) x.
Proof.
move => Hf Hg Hlg Hl.
apply ex_lim_mult ; try assumption.
now apply ex_lim_inv.
Admitted.

Lemma Lim_div (f g : R -> R) (x : Rbar) : ex_lim f x -> ex_lim g x -> Lim g x <> 0 -> ex_Rbar_div (Lim f x) (Lim g x) -> Lim (fun y => f y / g y) x = Rbar_div (Lim f x) (Lim g x).
Proof.
move => Hf Hg Hlg Hl.
apply is_lim_unique.
Admitted.

Lemma is_lim_comp_lin (f : R -> R) (a b : R) (x l : Rbar) : is_lim f (Rbar_plus (Rbar_mult a x) b) l -> a <> 0 -> is_lim (fun y => f (a * y + b)) x l.
Proof.
move => Hf Ha.
apply is_lim_comp with (Rbar_plus (Rbar_mult a x) b).
by apply Hf.
eapply is_lim_plus.
apply is_lim_scal_l.
apply is_lim_id.
apply is_lim_const.
apply Rbar_plus_correct.
case: (Rbar_mult a x) => //.
case: x {Hf} => [x | | ] //=.
exists (mkposreal _ Rlt_0_1) => y _ Hy.
apply Rbar_finite_neq, Rminus_not_eq ; ring_simplify (a * y + b - (a * x + b)).
rewrite -Rmult_minus_distr_l.
apply Rmult_integral_contrapositive ; split.
by [].
by apply Rminus_eq_contra.
exists 0 => x Hx.
apply sym_not_eq in Ha.
case: Rle_dec => // H.
case: Rle_lt_or_eq_dec => //.
exists 0 => x Hx.
apply sym_not_eq in Ha.
case: Rle_dec => // H.
Admitted.

Lemma ex_lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) : ex_lim f (Rbar_plus (Rbar_mult a x) b) -> ex_lim (fun y => f (a * y + b)) x.
Proof.
case => l Hf.
case: (Req_dec a 0) => [-> {a Hf} | Ha].
apply ex_lim_ext with (fun _ => f b).
move => y ; by rewrite Rmult_0_l Rplus_0_l.
by apply ex_lim_const.
Admitted.

Lemma Lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) : ex_lim f (Rbar_plus (Rbar_mult a x) b) -> a <> 0 -> Lim (fun y => f (a * y + b)) x = Lim f (Rbar_plus (Rbar_mult a x) b).
Proof.
move => Hf Ha.
apply is_lim_unique.
apply is_lim_comp_lin.
by apply Lim_correct.
Admitted.

Lemma is_lim_continuity (f : R -> R) (x : R) : continuity_pt f x -> is_lim f x (f x).
Proof.
intros cf.
Admitted.

Lemma ex_lim_continuity (f : R -> R) (x : R) : continuity_pt f x -> ex_finite_lim f x.
Proof.
move => Hf.
exists (f x).
Admitted.

Lemma Lim_continuity (f : R -> R) (x : R) : continuity_pt f x -> Lim f x = f x.
Proof.
move => Hf.
apply is_lim_unique.
Admitted.

Lemma C0_extension_right {T : UniformSpace} (f : R -> T) lb (a b : R) : a < b -> (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) -> (filterlim f (at_left b) (locally lb)) -> {g : R -> T | (forall c, a < c -> filterlim g (locally c) (locally (g c))) /\ (forall c : R, c < b -> g c = f c) /\ g b = lb}.
Proof.
intros Hab ; intros.
set g := fun x => match Rlt_dec x b with | left _ => f x | right _ => lb end.
assert (Gab : forall c : R, c < b -> g c = f c).
intros c Hcb.
unfold g.
by (case: Rlt_dec).
assert (Gb : forall c : R, b <= c -> g c = lb).
intros c Hbc.
unfold g.
case: Rlt_dec (Rle_not_lt _ _ Hbc) => //.
exists g ; split.
intros c Hac.
case: (Rlt_le_dec c b) ; (try case) => Hbc.
-
apply filterlim_ext_loc with f.
apply locally_interval with m_infty b => //= y _ Hyb.
by apply sym_eq, Gab.
rewrite Gab //.
apply H ; by split.
-
rewrite Gb.
2: by apply Rlt_le.
eapply filterlim_ext_loc.
2: by apply filterlim_const.
apply locally_interval with b p_infty => //= y Hby _.
apply sym_eq, Gb.
by apply Rlt_le.
-
rewrite -Hbc => {c Hbc Hac}.
rewrite Gb.
2: by apply Rle_refl.
apply filterlim_locally => eps /= {H}.
destruct (proj1 (filterlim_locally _ _) H0 eps) as [d Hd].
simpl in Hd.
exists d => x Hx.
case: (Rlt_le_dec x b) => Hxb.
rewrite Gab //.
by apply Hd.
rewrite Gb //.
by apply ball_center.
-
split.
by apply Gab.
Admitted.

Lemma filterlim_Ropp_right (x : R) : filterlim Ropp (at_right x) (at_left (- x)).
Proof.
move => P [d /= Hd].
exists d => y /= Hy Hy'.
apply Hd.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
rewrite -Ropp_plus_distr Rabs_Ropp.
by apply Hy.
Admitted.

Lemma C0_extension_left {T : UniformSpace} (f : R -> T) la (a b : R) : a < b -> (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) -> (filterlim f (at_right a) (locally la)) -> {g : R -> T | (forall c, c < b -> filterlim g (locally c) (locally (g c))) /\ (forall c : R, a < c -> g c = f c) /\ g a = la}.
Proof.
intros.
destruct (C0_extension_right (fun x => f (- x)) la (-b) (-a)) as [g Hg].
by apply Ropp_lt_contravar.
intros.
eapply filterlim_comp.
apply (filterlim_opp c).
apply H0.
split ; apply Ropp_lt_cancel ; rewrite Ropp_involutive ; by apply H2.
eapply filterlim_comp.
apply filterlim_Ropp_left.
by rewrite Ropp_involutive.
exists (fun x => g (- x)) ; split.
intros c Hc.
eapply filterlim_comp.
apply (filterlim_opp c).
by apply Hg, Ropp_lt_contravar.
split.
intros c Hc.
rewrite (proj1 (proj2 Hg)).
by rewrite Ropp_involutive.
by apply Ropp_lt_contravar.
Admitted.

Lemma C0_extension_lt {T : UniformSpace} (f : R -> T) la lb (a b : R) : a < b -> (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) -> (filterlim f (at_right a) (locally la)) -> (filterlim f (at_left b) (locally lb)) -> {g : R -> T | (forall c, filterlim g (locally c) (locally (g c))) /\ (forall c : R, a < c < b -> g c = f c) /\ g a = la /\ g b = lb}.
Proof.
intros.
destruct (C0_extension_left f la a b) as [g [Cg [Gab Ga]]] => //.
destruct (C0_extension_right g lb a b) as [h [Ch [Hab Hb]]] => //.
intros.
apply Cg, H3.
eapply filterlim_ext_loc.
2: by apply H2.
apply Rminus_lt_0 in H.
exists (mkposreal _ H) => y /= Hy Hy'.
apply sym_eq, Gab.
apply Ropp_lt_cancel, (Rplus_lt_reg_l b).
eapply Rle_lt_trans, Hy.
rewrite -abs_opp opp_minus.
apply Rle_abs.
exists h ; repeat split.
intros c.
case: (Rlt_le_dec a c) => Hac.
by apply Ch.
rewrite Hab.
eapply filterlim_ext_loc.
2: apply Cg.
apply locally_interval with m_infty b => //.
by eapply Rle_lt_trans, H.
intros y _ Hy ; by apply sym_eq, Hab.
by eapply Rle_lt_trans, H.
by eapply Rle_lt_trans, H.
intros c [Hac Hcb].
rewrite Hab => //.
by apply Gab.
by rewrite Hab.
Admitted.

Lemma C0_extension_le {T : UniformSpace} (f : R -> T) (a b : R) : (forall c : R, a <= c <= b -> filterlim f (locally c) (locally (f c))) -> {g : R -> T | (forall c, filterlim g (locally c) (locally (g c))) /\ (forall c : R, a <= c <= b -> g c = f c)}.
Proof.
intros.
case: (Rlt_le_dec a b) => Hab.
destruct (C0_extension_lt f (f a) (f b) a b Hab) as [g [Cg [Gab [Ga Gb]]]].
intros c Hc.
apply H ; split ; apply Rlt_le, Hc.
eapply filterlim_filter_le_1, H.
by apply filter_le_within.
intuition.
eapply filterlim_filter_le_1, H.
by apply filter_le_within.
intuition.
exists g ; repeat split => //.
intros c [Hac Hcb].
case: Hac => [ Hac | <-] //.
case: Hcb => [ Hcb | ->] //.
apply Gab ; by split.
exists (fun _ => f a) ; split ; simpl.
move => c.
by apply filterlim_const.
intros c [Hac Hca].
case: Hab => Hab.
contradict Hab ; apply Rle_not_lt.
by apply Rle_trans with c.
rewrite Hab in Hca.
Admitted.

Lemma bounded_continuity {K : AbsRing} {V : NormedModule K} (f : R -> V) a b : (forall x, a <= x <= b -> filterlim f (locally x) (locally (f x))) -> {M : R | forall x, a <= x <= b -> norm (f x) < M}.
Proof.
destruct (Rle_dec b a) as [Hab|Hab].
exists (norm (f a) + 1).
intros x [Hax Hxb].
replace x with a.
rewrite -{1}(Rplus_0_r (norm (f a))).
apply Rplus_lt_compat_l, Rlt_0_1.
apply Rle_antisym with (1 := Hax).
now apply Rle_trans with b.
apply Rnot_le_lt in Hab.
wlog: f / (forall x, filterlim f (locally x) (locally (f x))) => [ Hw Cf | Cf _ ].
destruct (C0_extension_le f a b) as [g [Cg Hg]].
by apply Cf.
destruct (Hw g) as [M HM] => //.
exists M ; intros.
rewrite -Hg //.
by apply HM.
assert (forall x : R, locally x (fun y : R => Rabs (norm (f y) - norm (f x)) < 1)).
intro x.
generalize (proj1 (filterlim_locally_ball_norm _ _) (Cf x)) => {Cf} Cf.
apply: filter_imp (Cf (mkposreal _ Rlt_0_1)) => y Hy.
apply Rle_lt_trans with (2 := Hy).
apply norm_triangle_inv.
assert (forall x y : R, Rabs (norm (f y) - norm (f x)) < 1 \/ ~ Rabs (norm (f y) - norm (f x)) < 1).
intros x y ; edestruct Rlt_dec.
left ; by apply r.
by right.
set delta := (fun (x : R) => proj1_sig (locally_ex_dec x _ (H0 x) (H x))).
destruct (compactness_value_1d a b delta) as [d Hd].
destruct (nfloor_ex ((b - a) / d)) as [N HN].
apply Rdiv_le_0_compat.
now apply Rlt_le, Rlt_Rminus.
apply cond_pos.
set (M := (fix g n := match n with O => 0 | S n => Rmax (norm (f (a + INR n * d)) + 3) (g n) end) (S N)).
exists M => x Hx.
apply Rnot_le_lt => H2.
apply (Hd x Hx) ; case => t.
unfold delta.
case: locally_ex_dec => e /= He [Ht [Hxt Hde]].
contradict H2 ; apply Rlt_not_le.
move: (fun (y : R) Hy => He y (norm_compat1 _ _ _ Hy)) => {He} He.
apply He in Hxt.
rewrite -(Rabs_pos_eq (norm _) (norm_ge_0 _)).
replace (norm (f x)) with ((norm (f x) - norm (f t)) + norm (f t))%R by ring.
eapply Rle_lt_trans.
apply Rabs_triang.
eapply Rlt_trans.
apply Rplus_lt_compat_r.
by apply Hxt.
rewrite Rplus_comm ; apply Rlt_minus_r.
clear x Hx Hxt.
destruct (nfloor_ex ((t - a) / d)) as [n Hn].
apply Rdiv_le_0_compat.
apply Rplus_le_reg_r with a.
now ring_simplify.
apply cond_pos.
set (y := a + INR n * d).
replace (norm (f t)) with (-(norm (f y) - norm (f t)) + norm (f y))%R by ring.
eapply Rle_lt_trans.
apply Rabs_triang.
eapply Rlt_trans.
apply Rplus_lt_compat_r.
rewrite Rabs_Ropp.
apply He.
change (Rabs (a + INR n * d - t) < e).
replace (a + INR n * d - t) with (-((t - a) / d - INR n) * d).
rewrite Rabs_mult (Rabs_pos_eq d).
2: apply Rlt_le, cond_pos.
apply Rlt_le_trans with (1 * d).
apply Rmult_lt_compat_r with (1 := cond_pos d).
rewrite Rabs_Ropp Rabs_pos_eq.
apply Rplus_lt_reg_r with (INR n).
now rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r (Rplus_comm 1).
apply Rplus_le_reg_r with (INR n).
now ring_simplify.
now rewrite Rmult_1_l.
field.
apply Rgt_not_eq, cond_pos.
apply Rplus_lt_reg_l with 1.
ring_simplify.
rewrite -> Rabs_pos_eq by apply norm_ge_0.
assert (n < S N)%nat.
apply INR_lt.
apply Rle_lt_trans with (1 := proj1 Hn).
rewrite S_INR.
apply Rle_lt_trans with (2 := proj2 HN).
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat, cond_pos.
now apply Rplus_le_compat_r.
unfold M, y.
clear -H1.
induction N.
apply Rlt_le_trans with (2 := Rmax_l _ _).
destruct n.
apply Rplus_lt_compat_l, Rplus_lt_compat_l.
now apply (IZR_lt 1 2).
now apply lt_S_n in H1.
destruct (le_lt_eq_dec _ _ (lt_n_Sm_le _ _ H1)) as [H2|H2].
apply Rlt_le_trans with (2 := Rmax_r _ _).
now apply IHN.
apply Rlt_le_trans with (2 := Rmax_l _ _).
rewrite H2.
apply Rplus_lt_compat_l, Rplus_lt_compat_l.
Admitted.

Lemma is_lim_le_loc (f g : R -> R) (x lf lg : Rbar) : Rbar_locally' x (fun y => f y <= g y) -> is_lim f x lf -> is_lim g x lg -> Rbar_le lf lg.
Proof.
Admitted.

Lemma is_lim_le_p_loc (f g : R -> R) (x : Rbar) : Rbar_locally' x (fun y => f y <= g y) -> is_lim f x p_infty -> is_lim g x p_infty.
Proof.
Admitted.

Lemma is_lim_le_m_loc (f g : R -> R) (x : Rbar) : Rbar_locally' x (fun y => g y <= f y) -> is_lim f x m_infty -> is_lim g x m_infty.
Proof.
Admitted.

Lemma is_lim_le_le_loc (f g h : R -> R) (x : Rbar) (l : Rbar) : Rbar_locally' x (fun y => f y <= h y <= g y) -> is_lim f x l -> is_lim g x l -> is_lim h x l.
Proof.
Admitted.

Lemma IVT_gen (f : R -> R) (a b y : R) : Ranalysis1.continuity f -> Rmin (f a) (f b) <= y <= Rmax (f a) (f b) -> { x : R | Rmin a b <= x <= Rmax a b /\ f x = y }.
Proof.
case: (Req_EM_T a b) => [ <- {b} | Hab].
rewrite /Rmin /Rmax ; case: Rle_dec (Rle_refl a) (Rle_refl (f a)) ; case: Rle_dec => // _ _ _ _ Cf Hy.
exists a ; split.
split ; by apply Rle_refl.
apply Rle_antisym ; by apply Hy.
wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
case: (Rle_lt_dec a b) => Hab'.
case: (Rle_lt_or_eq_dec _ _ Hab') => {Hab'} // Hab'.
by apply Hw.
rewrite (Rmin_comm (f a)) (Rmin_comm a) (Rmax_comm (f a)) (Rmax_comm a) ; apply Hw => //.
by apply Rlt_not_eq.
rewrite /(Rmin a) /(Rmax a) ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
wlog: f y / (f a <= f b) => [Hw |].
case: (Rle_lt_dec (f a) (f b)) => Hf' Hf Hy.
by apply Hw.
case: (Hw (fun y => - f y) (- y)).
by apply Ropp_le_contravar, Rlt_le.
by apply Ranalysis1.continuity_opp.
rewrite Rmin_opp_Rmax Rmax_opp_Rmin ; split ; apply Ropp_le_contravar, Hy.
move => x [Hx Hfx].
exists x ; intuition.
by rewrite -(Ropp_involutive y) -Hfx Ropp_involutive.
rewrite /Rmin /Rmax ; case: Rle_dec => // _ _.
wlog: y / (f a < y < f b) => [Hw Hf Hy | Hy Hf _].
case: Hy => Hay Hyb.
case: (Rle_lt_or_eq_dec _ _ Hay) => {Hay} [Hay | <- ].
case: (Rle_lt_or_eq_dec _ _ Hyb) => {Hyb} [Hyb | -> ].
apply Hw ; intuition.
exists b ; intuition.
exists a ; intuition.
case (IVT (fun x => f x - y) a b).
apply Ranalysis1.continuity_minus.
exact Hf.
apply continuity_const.
intros _ _ ; reflexivity.
exact Hab.
apply Rlt_minus_l ; rewrite Rplus_0_l ; apply Hy.
apply Rlt_minus_r ; rewrite Rplus_0_l ; apply Hy.
intros x [Hx Hfx].
apply Rminus_diag_uniq in Hfx.
Admitted.

Lemma filterlim_Ropp_left (x : R) : filterlim Ropp (at_left x) (at_right (- x)).
Proof.
move => P [d /= Hd].
exists d => y /= Hy Hy'.
apply Hd.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
rewrite -Ropp_plus_distr Rabs_Ropp.
by apply Hy.
by apply Ropp_lt_contravar.
