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

Lemma IVT_Rbar_incr (f : R -> R) (a b la lb : Rbar) (y : R) : is_lim f a la -> is_lim f b lb -> (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> continuity_pt f x) -> Rbar_lt a b -> Rbar_lt la y /\ Rbar_lt y lb -> {x : R | Rbar_lt a x /\ Rbar_lt x b /\ f x = y}.
Proof.
intros Hfa Hfb Cf Hab Hy.
assert (Hb' : exists b' : R, Rbar_lt b' b /\ is_upper_bound (fun x => Rbar_lt a x /\ Rbar_lt x b /\ f x <= y) b').
{
assert (Hfb' : Rbar_locally' b (fun x => y < f x)).
apply Hfb.
now apply (open_Rbar_gt' _ y).
clear -Hab Hfb'.
destruct b as [b| |].
-
destruct Hfb' as [eps He].
exists (b - eps).
split.
apply Rminus_lt_0.
replace (b - (b - eps)) with (pos eps) by ring.
apply cond_pos.
intros u [_ [H1 H2]].
apply Rnot_lt_le.
intros Hu.
apply Rle_not_lt with (1 := H2).
apply He.
apply Rabs_lt_between'.
split.
exact Hu.
apply Rlt_le_trans with (1 := H1).
apply Rlt_le.
apply Rminus_lt_0.
replace (b + eps - b) with (pos eps) by ring.
apply cond_pos.
now apply Rlt_not_eq.
-
destruct Hfb' as [M HM].
exists M.
repeat split.
intros u [_ [H1 H2]].
apply Rnot_lt_le.
intros Hu.
apply Rle_not_lt with (1 := H2).
now apply HM.
-
now destruct a.
}
assert (Hex : exists x : R, Rbar_lt a x /\ Rbar_lt x b /\ f x <= y).
{
assert (Hfa' : Rbar_locally' a (fun x => Rbar_lt x b /\ f x < y)).
apply filter_and.
apply Rbar_locally'_le.
now apply open_Rbar_lt'.
apply (Hfa (fun u => u < y)).
now apply (open_Rbar_lt' _ y).
clear -Hab Hfa'.
destruct a as [a| |].
-
destruct Hfa' as [eps He].
exists (a + eps / 2).
assert (Ha : a < a + eps / 2).
apply Rminus_lt_0.
replace (a + eps / 2 - a) with (eps / 2) by ring.
apply is_pos_div_2.
split.
exact Ha.
assert (H : Rbar_lt (a + eps / 2) b /\ (f (a + eps / 2) < y)).
apply He.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (a + eps / 2 + - a) with (eps / 2) by ring.
rewrite Rabs_pos_eq.
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_le.
apply is_pos_div_2.
now apply Rgt_not_eq.
destruct H as [H1 H2].
split.
exact H1.
now apply Rlt_le.
-
easy.
-
destruct Hfa' as [M HM].
exists (M - 1).
assert (H : Rbar_lt (M - 1) b /\ f (M - 1) < y).
apply HM.
apply Rminus_lt_0.
replace (M - (M - 1)) with 1 by ring.
apply Rlt_0_1.
destruct H as [H1 H2].
repeat split.
exact H1.
now apply Rlt_le.
}
destruct (completeness (fun x => Rbar_lt a x /\ Rbar_lt x b /\ f x <= y)) as [x [Hub Hlub]].
destruct Hb' as [b' Hb'].
now exists b'.
exact Hex.
exists x.
destruct Hb' as [b' [Hb Hb']].
destruct Hex as [x' Hx'].
assert (Hax : Rbar_lt a x).
apply Rbar_lt_le_trans with x'.
apply Hx'.
now apply Hub.
assert (Hxb : Rbar_lt x b).
apply Rbar_le_lt_trans with b'.
now apply Hlub.
exact Hb.
repeat split ; try assumption.
specialize (Cf _ Hax Hxb).
apply continuity_pt_filterlim in Cf.
destruct (total_order_T (f x) y) as [[H|H]|H].
-
assert (H': locally x (fun u => (Rbar_lt a u /\ Rbar_lt u b) /\ f u < y)).
apply filter_and.
apply filter_and.
now apply open_Rbar_gt.
now apply open_Rbar_lt.
apply (Cf (fun u => u < y)).
now apply open_lt.
destruct H' as [eps H'].
elim Rle_not_lt with x (x + eps / 2).
apply Hub.
destruct (H' (x + eps / 2)) as [[H1 H2] H3].
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (x + eps / 2 + - x) with (eps / 2) by ring.
rewrite Rabs_pos_eq.
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_le.
apply is_pos_div_2.
split.
exact H1.
split.
exact H2.
now apply Rlt_le.
apply Rminus_lt_0.
replace (x + eps / 2 - x) with (eps / 2) by ring.
apply is_pos_div_2.
-
exact H.
-
assert (H': locally x (fun u => y < f u)).
apply (Cf (fun u => y < u)).
now apply open_gt.
destruct H' as [eps H'].
elim Rle_not_lt with (x - eps) x.
apply Hlub.
intros u Hfu.
apply Rnot_lt_le.
intros Hu.
apply Rle_not_lt with (1 := proj2 (proj2 Hfu)).
apply H'.
apply Rabs_lt_between'.
split.
exact Hu.
apply Rle_lt_trans with (1 := Hub u Hfu).
apply Rminus_lt_0.
replace (x + eps - x) with (pos eps) by ring.
apply cond_pos.
apply Rminus_lt_0.
replace (x - (x - eps)) with (pos eps) by ring.
Admitted.

Lemma IVT_Rbar_decr (f : R -> R) (a b la lb : Rbar) (y : R) : is_lim f a la -> is_lim f b lb -> (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> continuity_pt f x) -> Rbar_lt a b -> Rbar_lt lb y /\ Rbar_lt y la -> {x : R | Rbar_lt a x /\ Rbar_lt x b /\ f x = y}.
Proof.
move => Hla Hlb Cf Hab Hy.
case: (IVT_Rbar_incr (fun x => - f x) a b (Rbar_opp la) (Rbar_opp lb) (-y)).
by apply is_lim_opp.
by apply is_lim_opp.
move => x Hax Hxb.
by apply continuity_pt_opp, Cf.
by apply Hab.
split ; apply Rbar_opp_lt ; rewrite Rbar_opp_involutive /Rbar_opp Ropp_involutive ; by apply Hy.
move => x Hx ; exists x ; intuition.
Admitted.

Lemma continuity_2d_pt_filterlim : forall f x y, continuity_2d_pt f x y <-> filterlim (fun z : R * R => f (fst z) (snd z)) (locally (x,y)) (locally (f x y)).
Proof.
split.
-
intros Cf P [eps He].
specialize (Cf eps).
apply locally_2d_locally in Cf.
apply filter_imp with (2 := Cf).
intros [u v].
apply He.
-
intros Cf eps.
apply locally_2d_locally.
specialize (Cf (fun z => Rabs (z - f x y) < eps)).
unfold filtermap in Cf.
apply Cf.
Admitted.

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

Lemma continuity_2d_pt_id1 : forall x y, continuity_2d_pt (fun u v => u) x y.
Proof.
intros x y eps; exists eps; tauto.
