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

Lemma RInt_Chasles : forall f a b c, ex_RInt f a b -> ex_RInt f b c -> plus (RInt f a b) (RInt f b c) = RInt f a c.
Proof.
intros f a b c H1 H2.
apply sym_eq, is_RInt_unique.
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

Lemma abs_RInt_le_const : forall (f : R -> R) a b M, a <= b -> ex_RInt f a b -> (forall t, a <= t <= b -> Rabs (f t) <= M) -> Rabs (RInt f a b) <= (b - a) * M.
Proof.
intros f a b M Hab If H.
apply: (norm_RInt_le_const f) => //.
Admitted.

Lemma ex_RInt_Reals_aux_1 (f : R -> R) (a b : R) : forall pr : Riemann_integrable f a b, is_RInt f a b (RiemannInt pr).
Proof.
wlog: a b / (a < b) => [Hw | Hab].
case: (total_order_T a b) => [[Hab | <-] | Hab] pr.
by apply Hw.
rewrite RiemannInt_P9.
apply: is_RInt_point.
move: (RiemannInt_P1 pr) => pr'.
rewrite (RiemannInt_P8 pr pr').
apply: is_RInt_swap.
apply Hw => //.
rewrite /is_RInt.
intros pr.
apply filterlim_locally.
unfold Riemann_fine.
rewrite Rmin_left.
2: now apply Rlt_le.
rewrite Rmax_right.
2: now apply Rlt_le.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
cut (forall (phi : StepFun a b) (eps : posreal), exists alpha : posreal, forall ptd : SF_seq, pointed_subdiv ptd -> seq_step (SF_lx ptd) < alpha -> SF_h ptd = a -> last (SF_h ptd) (unzip1 (SF_t ptd)) = b -> Rabs (RiemannInt_SF phi - 1 * Riemann_sum phi ptd) <= eps).
intros H.
rewrite /RiemannInt /= -/(Rminus _ _) => eps ; case: RiemannInt_exists => If HIf.
set eps2 := pos_div_2 eps.
set eps4 := pos_div_2 eps2.
case: (HIf _ (cond_pos eps4)) => {HIf} N HIf.
case: (nfloor_ex (/eps4) (Rlt_le _ _ (Rinv_0_lt_compat _ (cond_pos eps4)))) => n Hn.
move: (HIf (N+n)%nat (le_plus_l _ _)) => {HIf}.
rewrite /phi_sequence /R_dist ; case: pr => phi [psi pr] ; simpl RiemannInt_SF => HIf.
have H0 : Rabs (RiemannInt_SF psi) < eps4.
apply Rlt_le_trans with (1 := proj2 pr).
rewrite -(Rinv_involutive eps4 (Rgt_not_eq _ _ (cond_pos eps4))) /=.
apply Rle_Rinv.
apply Rinv_0_lt_compat, eps4.
intuition.
apply Rlt_le, Rlt_le_trans with (1 := proj2 Hn).
apply Rplus_le_compat_r.
apply le_INR, le_plus_r.
case: (H phi eps4) => alpha0 Hphi.
case: (H psi eps4) => {H} alpha1 Hpsi.
have Halpha : (0 < Rmin alpha0 alpha1).
apply Rmin_case_strong => _ ; [apply alpha0 | apply alpha1].
set alpha := mkposreal _ Halpha.
exists alpha => ptd Hstep [Hsort [Ha Hb]].
rewrite (double_var eps) 1?(double_var (eps/2)) ?Rplus_assoc.
rewrite /ball /= /AbsRing_ball /= /abs /=.
rewrite Rabs_minus_sym.
replace (_-_) with (-(RiemannInt_SF phi - If) + (RiemannInt_SF phi - Riemann_sum f ptd)) ; [ | rewrite /scal /= /mult /= ; by ring_simplify ].
apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_le_compat.
rewrite Rabs_Ropp ; apply HIf.
clear HIf ; replace (_-_) with ((RiemannInt_SF phi - 1* Riemann_sum phi ptd) + (Riemann_sum phi ptd - Riemann_sum f ptd)) ; [ | by ring_simplify].
apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
apply Hphi => //.
apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_l.
rewrite -Ropp_minus_distr' Rabs_Ropp.
change Rminus with (@minus R_AbelianGroup).
rewrite -Riemann_sum_minus.
have H1 : (forall t : R, SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> Rabs (f t - phi t) <= psi t).
move => t Ht.
apply pr ; move: (Rlt_le _ _ Hab) ; rewrite /Rmin /Rmax ; case: Rle_dec => // _ _ ; rewrite -Ha -Hb //.
apply Rle_trans with (1 := Riemann_sum_norm (fun t => f t - phi t) _ _ Hsort H1).
apply Rle_trans with (1 := Rle_abs _).
replace (Riemann_sum psi ptd) with (-(RiemannInt_SF psi - 1* Riemann_sum psi ptd) + RiemannInt_SF psi) ; [ | by ring_simplify].
apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
rewrite Rabs_Ropp ; apply Hpsi => //.
apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_r.
apply Rlt_le, H0.
case => phi [lx [ly Hphi]] eps /= ; rewrite /RiemannInt_SF /subdivision /subdivision_val ; move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
clear pr.
move: (Rlt_le _ _ Hab) Hphi => {Hab} ; elim: lx ly eps a b => [ | lx0 lx IH] ly eps a b Hab.
case ; intuition ; by [].
case: lx IH ly => [ | lx1 lx] IH ; case => [ {IH} | ly0 ly] Had ; try by (case: Had ; intuition ; by []).
exists eps => ptd Hptd Hstep (*Hsort*) Ha Hb /=.
rewrite Riemann_sum_zero.
rewrite Rmult_0_r Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
by apply ptd_sort.
rewrite /SF_lx /= Hb Ha ; case: Had => {Ha Hb} _ [Ha [Hb _]] ; move: Ha Hb ; rewrite /Rmin /Rmax ; case: Rle_dec => // _ <- <- //.
set eps2 := pos_div_2 eps ; set eps4 := pos_div_2 eps2.
case: (IH ly eps4 lx1 b) => {IH}.
replace b with (last 0 (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx)))).
apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1%nat) with (x0 := 0).
apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
simpl ; apply lt_n_S, lt_O_Sn.
case: Had => /= _ [_ [Hb _]] ; move: Hb ; rewrite /Rmax ; case : Rle_dec => //= _ ; elim: (lx) lx1 => //= h s IH _ ; apply IH.
apply (StepFun_P7 Hab Had).
move => /= alpha1 IH.
cut (forall eps : posreal, exists alpha : posreal, forall ptd : SF_seq, pointed_subdiv ptd -> seq_step (SF_lx ptd) < alpha -> SF_h ptd = a -> last (SF_h ptd) (SF_lx ptd) = lx1 -> Rabs (ly0 * (lx1 - lx0) - Riemann_sum phi ptd) <= eps).
intros H.
case: (H eps4) => {H} alpha2 H.
set fmin1 := foldr Rmin 0 (ly0::Rlist2seq ly).
set fmin2 := foldr Rmin 0 (map phi (lx0::lx1::Rlist2seq lx)).
set fmin := Rmin fmin1 fmin2.
set fmax1 := foldr Rmax 0 (ly0::Rlist2seq ly).
set fmax2 := foldr Rmax 0 (map phi (lx0::lx1::Rlist2seq lx)).
set fmax := Rmax fmax1 fmax2.
have Ha3 : (0 < eps4 / (Rmax (fmax - fmin) 1)).
apply Rdiv_lt_0_compat ; [ apply eps4 | ].
apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
set alpha3 := mkposreal _ Ha3.
have Halpha : (0 < Rmin (Rmin alpha1 alpha2) alpha3).
apply Rmin_case_strong => _ ; [ | apply alpha3].
apply Rmin_case_strong => _ ; [ apply alpha1 | apply alpha2].
set alpha := mkposreal _ Halpha.
exists alpha => ptd Hptd Hstep Ha Hb.
suff Hff : forall x, a <= x <= b -> fmin <= phi x <= fmax.
suff Hab1 : forall i, (i <= SF_size ptd)%nat -> a <= nth 0 (SF_lx ptd) i <= b.
suff Hab0 : a <= lx1 <= b.
rewrite (SF_Chasles _ _ lx1 (SF_h ptd)) /=.
replace (_-_) with ((ly0 * (lx1 - lx0) - 1* Riemann_sum phi (SF_cut_down' ptd lx1 (SF_h ptd))) + (Int_SF ly (RList.cons lx1 lx) - 1* Riemann_sum phi (SF_cut_up' ptd lx1 (SF_h ptd)))) ; [ | rewrite /plus /= ; by ring_simplify].
rewrite (double_var eps) ; apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
set ptd_r_last := (SF_last a (SF_cut_down' ptd lx1 a)).
set ptd_r_belast := (SF_belast (SF_cut_down' ptd lx1 a)).
set ptd_r := SF_rcons ptd_r_belast (lx1, (fst (SF_last a ptd_r_belast) + lx1)/2).
move: (H ptd_r) => {H} H.
replace (_-_) with ((ly0 * (lx1 - lx0) - Riemann_sum phi ptd_r) + (phi ((fst (SF_last 0 ptd_r_belast) + lx1)/2) - phi (snd ptd_r_last)) * (lx1 - fst (SF_last 0 ptd_r_belast))).
rewrite (double_var (eps/2)) ; apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
apply: H => {IH}.
Focus 3.
rewrite -Ha /ptd_r /ptd_r_belast.
move: (proj1 Hab0) ; rewrite -Ha.
apply SF_cons_dec with (s := ptd) => [x0 | [x0 y0] s] //= Hx0 ; by case: Rle_dec.
Focus 3.
revert ptd_r_belast ptd_r ; move: (proj1 Hab0) ; rewrite -Ha ; apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH] //= Hx0 ; case: Rle_dec => //= _.
by rewrite unzip1_rcons /= last_rcons.
revert ptd_r_belast ptd_r Hptd ; apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH ] Hptd.
rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
rewrite ?unzip2_rcons ?unzip1_rcons /=.
rewrite ?unzip1_belast ?unzip2_belast /=.
rewrite ?unzip1_behead ?unzip2_behead /=.
case => /= [ _ | i Hi] .
case: Rle_dec => //= Hx0 ; lra.
contradict Hi ; apply le_not_lt.
case: Rle_dec => //= Hx0 ; rewrite /SF_size /= ; apply le_n_S, le_O_n.
move: (IH (ptd_cons _ _ Hptd)) => {IH} IH.
case => [ _ | i Hi].
rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
rewrite ?unzip2_rcons ?unzip1_rcons /=.
rewrite ?unzip1_belast ?unzip2_belast /=.
rewrite ?unzip1_behead ?unzip2_behead /=.
case: Rle_dec => //= Hx0.
case: Rle_dec => //= Hx1.
move: Hptd Hx1 ; apply SF_cons_dec with (s := s) => {s IH} /= [x1 | [x1 y1] s] //= Hptd Hx1.
by apply (Hptd O (lt_O_Sn _)).
case: Rle_dec => //= Hx2.
by apply (Hptd O (lt_O_Sn _)).
by apply (Hptd O (lt_O_Sn _)).
lra.
lra.
move: Hi (IH i) => {IH}.
rewrite ?SF_size_rcons -?SF_size_lx ?SF_lx_rcons ?SF_ly_rcons.
rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
rewrite -?(last_map (@fst R R)) -?unzip1_fst.
rewrite ?unzip2_rcons ?unzip1_rcons /=.
rewrite ?unzip1_belast ?unzip2_belast /=.
rewrite ?unzip1_behead ?unzip2_behead /=.
case: (Rle_dec x0 lx1) => //= Hx0.
case: (Rle_dec (SF_h s) lx1) => //= Hx1.
rewrite size_belast size_belast'.
move: Hx1 ; apply SF_cons_dec with (s := s) => {s Hptd} /= [ x1 | [x1 y1] s] //= Hx1.
move => Hi IH ; apply IH ; by apply lt_S_n.
case: Rle_dec => //= Hx2.
move => Hi IH ; apply IH ; by apply lt_S_n.
move => Hi IH ; apply IH ; by apply lt_S_n.
move => Hi ; by apply lt_S_n, lt_n_O in Hi.
move => Hi ; by apply lt_S_n, lt_n_O in Hi.
apply Rlt_le_trans with (2 := Rmin_r alpha1 alpha2) ; apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
apply Rle_lt_trans with (2 := Hstep) => {Hstep}.
move: Hab0 ; rewrite -Ha -Hb ; revert ptd_r_belast ptd_r => {Hab1} ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //= Hab0.
rewrite /SF_lx /SF_rcons /SF_belast /SF_last /SF_cut_down' /=.
move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) /seq_step /=.
rewrite Rminus_eq_0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
move: Hab0 (fun Hx1 => IH (conj Hx1 (proj2 Hab0))) => {IH}.
apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hab0 IH.
rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_lx /=.
move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
case: Rle_dec => //= Hx1.
rewrite /seq_step /=.
apply Rle_max_compat_l.
rewrite (Rle_antisym _ _ Hx1 (proj2 Hab0)) Rminus_eq_0 Rabs_R0.
apply Rmax_case_strong ; by intuition.
rewrite /seq_step /=.
apply Rle_max_compat_r.
apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
apply Rplus_le_compat_r.
by apply Rlt_le, Rnot_le_lt.
apply Rle_ge ; rewrite -Rminus_le_0 ; by apply Hab0.
move: IH ; rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_lx /=.
move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
case: (Rle_dec x1 lx1) => //= Hx1 IH.
move: (IH Hx1) => {IH}.
case: (Rle_dec (SF_h s) lx1) => //= Hx2.
rewrite /seq_step -?(last_map (@fst R R)) /= => IH ; apply Rle_max_compat_l, IH.
rewrite /seq_step /= ; apply Rle_max_compat_l.
rewrite /seq_step /= ; apply Rmax_le_compat.
apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
by apply Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
apply Rle_ge ; rewrite -Rminus_le_0 ; apply Hab0.
apply Rmax_case_strong => _.
apply Rabs_pos.
apply SF_cons_ind with (s := s) => {s IH Hab0} /= [x2 | [x2 y2] s IH] //=.
exact: Rle_refl.
apply Rmax_case_strong => _.
apply Rabs_pos.
exact: IH.
clear H IH.
apply Rle_trans with ((fmax - fmin) * alpha3).
rewrite Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
apply Rabs_le_between.
rewrite Ropp_minus_distr'.
suff H0 : a <= (fst (SF_last 0 ptd_r_belast) + lx1) / 2 <= b.
suff H1 : a <= snd ptd_r_last <= b.
split ; apply Rplus_le_compat, Ropp_le_contravar ; by apply Hff.
revert ptd_r_last Hab1 Hptd.
apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
rewrite /SF_cut_down' /= ; case: Rle_dec => //= ; by intuition.
rewrite SF_size_cons in Hab1.
move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
rewrite /SF_cut_down' /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; split.
apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
move => _ ; split.
apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
move => _ ; by intuition.
rewrite /SF_cut_down' /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec _ lx1) => //= Hx2'.
move => _ ; split.
apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
move => _ ; by intuition.
cut (a <= fst (SF_last 0 ptd_r_belast) <= b).
lra.
split.
revert ptd_r_belast ptd_r Hab1 Hptd.
apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
by apply (Hab1 O (le_O_n _)).
by apply Hab0.
rewrite SF_size_cons in Hab1.
move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hx0.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hab0.
rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec _ lx1) => //= Hx2'.
move => _ ; by apply Hx0.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hab0.
revert ptd_r_belast ptd_r Hab1 Hptd.
apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
by apply (Hab1 O (le_O_n _)).
by apply Hab0.
rewrite SF_size_cons in Hab1.
move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hx0.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hab0.
rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec _ lx1) => //= Hx2'.
move => _ ; by apply Hx0.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hab0.
apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
apply Rle_trans with (2 := Rlt_le _ _ Hstep).
rewrite Rabs_right.
rewrite -Ha -Hb in Hab0 ; revert ptd_r_belast ptd_r Hptd Hab0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
rewrite /SF_cut_down' /SF_belast /SF_last /seq_step /= => Hptd Hab0.
move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) ; apply Req_le ; by ring.
move => Hptd Hab0 ; move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
rewrite /SF_cut_down' /SF_belast /SF_last /=.
move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
case: (Rle_dec (SF_h s)) => //= Hx1 IH.
move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
rewrite /seq_step /= => IH.
apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
case: (Rle_dec (SF_h s)) => //= Hx2 IH.
move: Hx2 IH ; apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
rewrite /seq_step /= => IH.
apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
case: (Rle_dec (SF_h s)) => //= Hx3 IH.
apply Rle_trans with (1 := IH).
rewrite /seq_step /= ; by apply RmaxLess2.
rewrite /seq_step /=.
apply Rle_trans with (2 := RmaxLess2 _ _).
apply Rle_trans with (2 := RmaxLess2 _ _).
apply Rle_trans with (2 := RmaxLess1 _ _).
apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx3.
rewrite /seq_step /=.
apply Rle_trans with (2 := RmaxLess2 _ _).
apply Rle_trans with (2 := RmaxLess1 _ _).
apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx2.
rewrite /seq_step /=.
apply Rle_trans with (2 := RmaxLess1 _ _).
apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
apply Rle_ge ; rewrite -Rminus_le_0.
revert ptd_r_belast ptd_r ; rewrite -Ha in Hab0 ; move: (proj1 Hab0) ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
rewrite /SF_cut_down' /SF_belast /SF_last /=.
by case: Rle_dec.
move: IH ; rewrite /SF_cut_down' /SF_belast /SF_last /=.
case: (Rle_dec x0 _) => //= _.
case: (Rle_dec (SF_h s) _) => //= Hx1 IH.
move: Hx1 (IH Hx1) => {IH}.
apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
case: (Rle_dec (SF_h s) _) => //=.
apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] //= Hx2.
case: (Rle_dec (SF_h s) _) => //=.
rewrite /alpha3 /=.
apply (Rmax_case_strong (fmax - fmin)) => H.
apply Req_le ; field.
apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
apply Rmult_le_compat_r, H.
apply Rlt_le, eps4.
clear H IH.
rewrite Rplus_assoc Rmult_1_l.
apply (f_equal (Rplus (ly0 * (lx1 - lx0)))).
rewrite -(Ropp_involutive (-_+_)).
apply Ropp_eq_compat.
rewrite Ropp_plus_distr Ropp_involutive.
revert ptd_r_last ptd_r_belast ptd_r ; move: (proj1 Hab0) ; rewrite -Ha => {Hab0} ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
rewrite /SF_cut_down' /=.
case: (Rle_dec x0 lx1) => //= _.
rewrite /Riemann_sum /= /plus /zero /scal /= /mult /=.
by ring.
case: (Rle_dec (SF_h s) lx1) => //= Hx1.
move: Hx1 (IH Hx1) => {IH}.
apply SF_cons_dec with (s := s) => {s} [x1 | [x1 y1] s] /= Hx1.
rewrite /SF_cut_down' /= ; case: (Rle_dec x0 _) => //= _ ; case: (Rle_dec x1 _) => //= _.
rewrite /Riemann_sum /= => _.
rewrite /plus /zero /scal /= /mult /=.
ring.
rewrite /SF_cut_down' /= ; case: (Rle_dec x0 _) => //= _ ; case: (Rle_dec x1 _) => //= _ ; case: (Rle_dec (SF_h s) _) => //= Hx2.
rewrite /SF_belast /SF_last /SF_rcons /=.
rewrite (Riemann_sum_cons phi (x0,y0) ({| SF_h := x1; SF_t := (SF_h s, y1) :: seq_cut_down' (SF_t s) lx1 y1 |})).
rewrite (Riemann_sum_cons phi (x0,y0) ({| SF_h := x1; SF_t := rcons (seq.belast (SF_h s, y1) (seq_cut_down' (SF_t s) lx1 y1)) (lx1, (fst (last (x1, y0) (seq.belast (SF_h s, y1) (seq_cut_down' (SF_t s) lx1 y1))) + lx1) / 2) |})).
move => <- /=.
rewrite Rplus_assoc ; apply f_equal.
rewrite -!(last_map (@fst R R)) -!unzip1_fst /=.
ring.
rewrite /Riemann_sum /= => _.
rewrite /plus /zero /scal /= /mult /=.
ring.
rewrite /SF_cut_down' /= ; case: Rle_dec => //= _ ; case: Rle_dec => //= _.
rewrite /Riemann_sum /= /plus /zero /scal /= /mult /=.
ring.
set ptd_l_head := (SF_head a (SF_cut_up' ptd lx1 a)).
set ptd_l_behead := (SF_behead (SF_cut_up' ptd lx1 a)).
set ptd_l := SF_cons (lx1, (lx1 + fst (SF_head a ptd_l_behead))/2) ptd_l_behead.
move: (IH ptd_l) => {IH} IH.
replace (_-_) with ((Int_SF ly (RList.cons lx1 lx) - 1 * Riemann_sum phi ptd_l) - (phi ((lx1 + fst (SF_head 0 ptd_l_behead))/2) - phi (snd ptd_l_head)) * (lx1 - fst (SF_head 0 ptd_l_behead))).
rewrite (double_var (eps/2)) ; apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
apply: IH.
case.
move => _ ; move: (proj1 Hab0) ; rewrite -Ha => /= Hx0 ; case: Rle_dec => //= _.
rewrite seq_cut_up_head'.
move: Hx0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
split ; apply Req_le ; field.
case: Rle_dec => //= Hx1.
move: Hx1 (IH Hx1) => {IH}.
apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
case: Rle_dec => //= Hx2.
lra.
rewrite /ptd_l SF_lx_cons SF_ly_cons SF_size_cons => i Hi ; move: i {Hi} (lt_S_n _ _ Hi).
revert ptd_l_behead ptd_l Hptd ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hptd.
rewrite /SF_cut_up' /=.
case: Rle_dec => //=.
rewrite /SF_size /SF_behead /= => _ i Hi ; by apply lt_n_O in Hi.
move: (IH (ptd_cons _ _ Hptd)) => {IH}.
rewrite /SF_cut_up' /=.
case: (Rle_dec x0 _) => //= Hx0.
case: (Rle_dec (SF_h s) _) => //= Hx1.
rewrite !seq_cut_up_head'.
move: Hx1 ; apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] //= Hx1.
case: (Rle_dec (SF_h s) _) => //= Hx2.
apply Rlt_le_trans with (2 := Rmin_l alpha1 alpha2).
apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
apply Rle_lt_trans with (2 := Hstep).
revert ptd_l_behead ptd_l ; move :(proj1 Hab0) ; rewrite -Ha ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] /= s IH] Hx0.
rewrite /SF_cut_up' /= ; case: (Rle_dec x0 _) => //= _.
rewrite /seq_step /= Rminus_eq_0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
rewrite /SF_cut_up' /= ; case: (Rle_dec x0 _) => //= _.
move: IH ; rewrite /SF_cut_up' /= ; case: (Rle_dec (SF_h s) _) => //= Hx1 ; rewrite ?seq_cut_up_head' => IH.
move: Hx1 (IH Hx1) => {IH} ; apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx1 IH.
apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; exact: RmaxLess2.
move: IH ; case: (Rle_dec (SF_h s) _) => //= Hx2 IH.
apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; exact: RmaxLess2.
apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ; exact: RmaxLess2.
clear IH ; rewrite /seq_step /=.
apply Rle_max_compat_r.
apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
by apply Rplus_le_compat_l, Ropp_le_contravar.
by apply Rle_ge, (Rminus_le_0 lx1 _), Rlt_le, Rnot_le_lt.
by rewrite /ptd_l /=.
rewrite -Hb.
move: (proj1 Hab0) ; rewrite -Ha /=; case: (Rle_dec (SF_h ptd) lx1) => //= _ _.
rewrite seq_cut_up_head'.
move: Hab0 ; rewrite -Ha -Hb ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= [Hx0 Hlx1].
by apply Rle_antisym.
move: (fun Hx1 => IH (conj Hx1 Hlx1)) => {IH} ; case: (Rle_dec (SF_h s) _) => //= Hx1.
move => IH ; rewrite -(IH Hx1) => {IH}.
move: Hx1 Hlx1 ; apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s ] Hx1 Hlx1.
by [].
case: (Rle_dec (SF_h s) _) => /= Hx2 ; by [].
clear H IH.
apply Rle_trans with ((fmax - fmin) * alpha3).
rewrite Rabs_Ropp Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
apply Rabs_le_between.
rewrite Ropp_minus_distr'.
suff H0 : a <= (lx1 + fst (SF_head 0 ptd_l_behead)) / 2 <= b.
suff H1 : a <= snd ptd_l_head <= b.
split ; apply Rplus_le_compat, Ropp_le_contravar ; by apply Hff.
revert ptd_l_head Hab1 Hptd.
apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
rewrite /SF_cut_up' /= ; case: Rle_dec => //= ; by intuition.
rewrite SF_size_cons in Hab1.
move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
rewrite /SF_cut_up' /SF_head /=.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; split.
apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
move => _ ; by intuition.
rewrite /SF_cut_up' /SF_head /=.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec _ lx1) => //= Hx2'.
move => _ ; split.
apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
move => _ ; by intuition.
cut (a <= fst (SF_head 0 ptd_l_behead) <= b).
lra.
split.
revert ptd_l_behead ptd_l Hab1 Hptd.
apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
by apply Hab0.
by apply (Hab1 O (le_O_n _)).
rewrite SF_size_cons in Hab1.
move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
rewrite /SF_cut_up' /SF_head /= -?(head_map (@fst R R)) -?unzip1_fst.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hx0.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec _ lx1) => //= Hx2'.
by rewrite ?seq_cut_up_head'.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hx0.
move => _ ; by apply Hx0.
revert ptd_l_behead ptd_l Hab1 Hptd.
apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
case: Rle_dec => //= Hx0.
by apply Hab0.
by apply (Hab1 O (le_O_n _)).
rewrite SF_size_cons in Hab1.
move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
rewrite -?(head_map (@fst R R)) -?unzip1_fst.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec x1 lx1) => //= Hx1'.
move => _ ; by apply Hx0.
move => _ ; by apply Hx0.
case: (Rle_dec x0 lx1) => //= Hx0'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec _ lx1) => //= Hx2'.
by rewrite !seq_cut_up_head'.
case: (Rle_dec x1 lx1) => //= Hx1'.
case: (Rle_dec _ lx1) => //= Hx2'.
move => _ ; by apply Hx0.
move => _ ; by apply Hx0.
move => _ ; by apply Hx0.
apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
apply Rle_trans with (2 := Rlt_le _ _ Hstep).
rewrite -Rabs_Ropp Rabs_right ?Ropp_minus_distr'.
rewrite -Ha -Hb in Hab0 ; revert ptd_l_behead ptd_l Hptd Hab0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
rewrite /seq_step /= => Hptd Hab0.
move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
apply Req_le ; by ring.
move => Hptd Hab0 ; move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
case: (Rle_dec (SF_h s)) => //= Hx1 IH.
move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
rewrite /seq_step /= => IH.
apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
case: (Rle_dec (SF_h s)) => //= Hx2 IH.
move: Hx2 IH ; apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
rewrite /seq_step /= => IH.
apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
case: (Rle_dec (SF_h s)) => //= Hx3 IH.
rewrite !seq_cut_up_head' in IH |-*.
apply Rle_trans with (1 := IH).
rewrite /seq_step /= ; by apply RmaxLess2.
rewrite /seq_step /=.
apply Rle_trans with (2 := RmaxLess2 _ _).
apply Rle_trans with (2 := RmaxLess2 _ _).
apply Rle_trans with (2 := RmaxLess1 _ _).
by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
rewrite /seq_step /=.
apply Rle_trans with (2 := RmaxLess2 _ _).
apply Rle_trans with (2 := RmaxLess1 _ _).
by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
rewrite /seq_step /=.
apply Rle_trans with (2 := RmaxLess1 _ _).
apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar, Hab0.
apply Rle_ge, (Rminus_le_0 lx1).
revert ptd_l_behead ptd_l ; rewrite -Ha -Hb in Hab0 ; move: Hab0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
case: Rle_dec => /= _.
exact: Rle_refl.
exact: (proj2 Hx0).
move: (proj1 Hx0) ; case: Rle_dec => //= _ _.
move: (fun Hx1 => IH (conj Hx1 (proj2 Hx0))) => {IH}.
case: (Rle_dec (SF_h s)) => //= Hx1 IH.
rewrite !seq_cut_up_head' in IH |-* ; move: (IH Hx1) => {IH}.
move: Hx0 Hx1 ; apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx0 Hx1 IH.
exact: Rle_refl.
move: IH ; case: (Rle_dec (SF_h s)) => /= Hx2.
by [].
by [].
by apply Rlt_le, Rnot_le_lt, Hx1.
rewrite /alpha3 /=.
apply (Rmax_case_strong (fmax - fmin)) => H.
apply Req_le ; field.
apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
apply Rmult_le_compat_r, H.
apply Rlt_le, eps4.
clear H IH.
rewrite !Rmult_1_l {1 2}/Rminus Rplus_assoc -Ropp_plus_distr.
apply (f_equal (Rminus _)) => /=.
rewrite /ptd_l /ptd_l_behead /ptd_l_head /= /SF_cut_up' /= ; move: Hab0 ; rewrite -Ha -Hb /= ; case => [Hx0 Hlx1].
case: (Rle_dec (SF_h ptd)) => //= _.
rewrite ?seq_cut_up_head' /SF_ly /= Riemann_sum_cons /=.
move: Hx0 Hlx1 ; apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s /= IH] /= Hx0 Hlx1.
rewrite /Riemann_sum /= /plus /zero /scal /= /mult /= ; ring.
case: (Rle_dec (SF_h s)) => //= Hx1.
move: (IH Hx1 Hlx1) => /= {IH}.
move: Hx1 Hlx1 ; apply SF_cons_dec with (s := s) => {s} [x1 | [x1 y1] s /=] /= Hx1 Hlx1 IH.
rewrite /Riemann_sum /= /plus /zero /scal /= /mult /= ; ring.
move: IH ; case: (Rle_dec (SF_h s)) => //= Hx2.
move => <- ; apply Rminus_diag_uniq ; ring_simplify.
move: Hx2 Hlx1 y1 ; apply SF_cons_ind with (s := s) => {s} [x2 | [x2 y2] s /= IH] /= Hx2 Hlx1 y1.
ring.
case: (Rle_dec (SF_h s)) => //= Hx3.
by apply IH.
ring.
rewrite /Riemann_sum /= /plus /zero /scal /= /mult /=.
ring_simplify.
repeat apply f_equal.
by elim: (SF_t s) (0) (y0).
replace (fst (last (SF_h ptd, SF_h ptd) (SF_t ptd))) with (last (SF_h ptd) (unzip1 (SF_t ptd))).
Focus 2.
pattern (SF_h ptd) at 1.
replace (SF_h ptd) with (fst (SF_h ptd, SF_h ptd)) by auto.
elim: (SF_t ptd) (SF_h ptd, SF_h ptd) => //=.
by rewrite Hb Ha.
replace lx1 with (pos_Rl (RList.cons lx0 (RList.cons lx1 lx)) 1) by reflexivity.
move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ; case: Rle_dec => // _ <- <-.
rewrite -(seq2Rlist_bij (RList.cons lx0 _)) !nth_compat size_compat.
split.
rewrite nth0.
apply (sorted_head (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1).
apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
simpl ; by apply lt_n_S, lt_O_Sn.
simpl ; rewrite -last_nth.
apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1) with (x0 := 0).
apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
simpl ; by apply lt_n_S, lt_O_Sn.
rewrite -Ha -Hb /SF_lx /= => i Hi.
apply le_lt_n_Sm in Hi ; rewrite -SF_size_lx /SF_lx in Hi.
split.
exact: (sorted_head (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).
exact: (sorted_last (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).
clear H IH.
move => x Hx ; case: (sorted_dec ([:: lx0, lx1 & Rlist2seq lx]) 0 x).
apply sorted_compat ; rewrite /= seq2Rlist_bij ; apply Had.
move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ; case: Rle_dec => // _.
rewrite -nth0 -nth_last /= => -> Hb'.
split.
by apply Hx.
elim: (lx) (lx1) Hb' => /= [ | h1 s IH] h0 Hb'.
rewrite Hb' ; by apply Hx.
by apply IH.
case => i ; case ; case ; case => {Hx} Hx Hx' Hi.
rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
split.
apply Rle_trans with (1 := Rmin_l _ _), H.
apply Rle_trans with (2 := RmaxLess1 _ _), H.
rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
have : (S i < size (ly0 :: Rlist2seq ly))%nat.
move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /= => -> ; exact: lt_S_n.
move: i {Hx Hx' Hi}.
elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
by apply lt_n_O in Hi.
case: i Hi => /= [ | i] Hi.
split ; [exact: Rmin_l | exact: RmaxLess1].
split ; [apply Rle_trans with (1 := Rmin_r _ _) | apply Rle_trans with (2 := RmaxLess2 _ _)] ; apply IH ; by apply lt_S_n.
simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ; by intuition.
split.
rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
rewrite -Hx.
suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
split.
apply Rle_trans with (1 := Rmin_r _ _), H.
apply Rle_trans with (2 := RmaxLess2 _ _), H.
rewrite /fmin2 /fmax2 .
move: i Hi {Hx Hx'}.
elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
by apply lt_n_O in Hi.
case: i Hi => /= [ | i] Hi.
split ; [exact: Rmin_l | exact: RmaxLess1].
split ; [apply Rle_trans with (1 := Rmin_r _ _) | apply Rle_trans with (2 := RmaxLess2 _ _)] ; apply IH ; by apply lt_S_n.
have : (((size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat) < size [:: lx0, lx1 & Rlist2seq lx])%nat.
by [].
replace (size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat with (S (size [:: lx0, lx1 & Rlist2seq lx] - 2)) by (simpl ; intuition).
move: (size [:: lx0, lx1 & Rlist2seq lx] - 2)%nat => i Hi.
case ; case => {Hx} Hx ; [ case => Hx' | move => _ ].
rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
split.
apply Rle_trans with (1 := Rmin_l _ _), H.
apply Rle_trans with (2 := RmaxLess1 _ _), H.
rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
have : (i < size (ly0 :: Rlist2seq ly))%nat.
move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /= => -> ; exact: lt_S_n.
move: i {Hx Hx' Hi}.
elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
by apply lt_n_O in Hi.
case: i Hi => /= [ | i] Hi.
split ; [exact: Rmin_l | exact: RmaxLess1].
split ; [apply Rle_trans with (1 := Rmin_r _ _) | apply Rle_trans with (2 := RmaxLess2 _ _)] ; apply IH ; by apply lt_S_n.
simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ; by intuition.
split.
rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
rewrite Hx'.
suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] (S i)) <= fmax2.
split.
apply Rle_trans with (1 := Rmin_r _ _), H.
apply Rle_trans with (2 := RmaxLess2 _ _), H.
rewrite /fmin2 /fmax2 .
move: i Hi {Hx Hx'}.
elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
by apply lt_n_O in Hi.
case: s IH Hi => /= [ | h1 s] IH Hi.
by apply lt_S_n, lt_n_O in Hi.
case: i Hi => /= [ | i] Hi.
split ; [ apply Rle_trans with (1 := Rmin_r _ _) ; exact: Rmin_l | apply Rle_trans with (2 := RmaxLess2 _ _) ; exact: RmaxLess1].
split ; [apply Rle_trans with (1 := Rmin_r _ _) | apply Rle_trans with (2 := RmaxLess2 _ _)] ; apply IH ; by apply lt_S_n.
rewrite -Hx.
suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
split.
apply Rle_trans with (1 := Rmin_r _ _), H.
apply Rle_trans with (2 := RmaxLess2 _ _), H.
rewrite /fmin2 /fmax2 .
move: i Hi {Hx}.
elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
by apply lt_n_O in Hi.
case: i Hi => /= [ | i] Hi.
split ; [exact: Rmin_l | exact: RmaxLess1].
split ; [apply Rle_trans with (1 := Rmin_r _ _) | apply Rle_trans with (2 := RmaxLess2 _ _)] ; apply IH ; by apply lt_S_n.
clear eps eps2 IH eps4 alpha1.
move: (proj1 (proj2 Had)) => /= ; rewrite /Rmin ; case: Rle_dec => //= _ <-.
move: (proj1 Had O (lt_O_Sn _)) => /= Hl0l1.
move: (proj2 (proj2 (proj2 (proj2 Had))) O (lt_O_Sn _)) => /= Hval.
clear a b Hab Had lx ly.
rename lx0 into a ; rename lx1 into b ; rename ly0 into c ; rename Hl0l1 into Hab.
set fmin := Rmin (Rmin (phi a) (phi b)) c.
set fmax := Rmax (Rmax (phi a) (phi b)) c.
move => eps ; set eps2 := pos_div_2 eps.
have Halpha : 0 < eps2 / (Rmax (fmax - fmin) 1).
apply Rdiv_lt_0_compat.
apply eps2.
apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
set alpha := mkposreal _ Halpha.
exists alpha => ptd.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd IH] Hptd Hstep Ha Hb ; simpl in Ha, Hb.
rewrite -Ha -Hb /Riemann_sum /= ; rewrite Rminus_eq_0 Rmult_0_r Rminus_0_r Rabs_R0.
by apply Rlt_le, eps.
move: (fun Ha => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep) Ha Hb) => {IH} IH.
move: (proj1 (ptd_sort _ Hptd)) ; rewrite Ha in Hptd, Hstep |- * => {x0 Ha} ; case => /= Ha.
rewrite Riemann_sum_cons /= /plus /zero /scal /= /mult /= => {IH}.
replace (_-_) with ((c-phi y0) * (SF_h ptd - a) + (c * (b - SF_h ptd) - Riemann_sum phi ptd)) by ring.
rewrite (double_var eps) ; apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
apply Rle_trans with ((fmax - fmin) * alpha).
rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
suff : a <= y0 <= b.
case ; case => Ha'.
case => Hb'.
rewrite Hval.
rewrite Rminus_eq_0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ; case: Rle_dec => // H0 H1 H2.
by apply Rlt_le, Rnot_le_lt, H1.
by apply Rle_refl.
by apply Rlt_le, Rnot_le_lt, H0.
by apply Rle_refl.
by apply Rlt_le, Rnot_le_lt, H0.
by split.
rewrite Hb' ; apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ; apply Rplus_le_compat, Ropp_le_contravar.
by apply Rmin_r.
by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
by apply RmaxLess2.
by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
rewrite -Ha' => _ ; apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ; apply Rplus_le_compat, Ropp_le_contravar.
by apply Rmin_r.
by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
by apply RmaxLess2.
by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
split.
apply (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_h ptd).
apply (Hptd O (lt_O_Sn _)).
rewrite -Hb ; apply (sorted_last (SF_lx ptd) 0 (proj2 (ptd_sort _ Hptd)) (lt_O_Sn _)) with (x0 := 0).
apply Rlt_le, Rle_lt_trans with (2 := Hstep) ; rewrite /seq_step /= ; apply RmaxLess1.
rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
apply Req_le ; field.
by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
apply Rlt_le, eps2.
apply H.
move: (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep : seq_step (SF_lx ptd) < alpha) Ha Hb => {Hptd Hstep y0} Hptd Hstep Ha Hb.
suff : SF_h ptd <= b.
case => Hx0.
move: Hptd Hstep Ha Hb Hx0.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | [x0 y0] ptd IH] Hptd Hstep /= Ha Hb Hx0.
contradict Hb ; apply Rlt_not_eq, Hx0.
move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep) (Rlt_le_trans _ _ _ Ha (proj1 (ptd_sort _ Hptd))) Hb Hx1) => {IH} IH.
rewrite Riemann_sum_cons /=.
have : SF_h ptd <= b.
rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
apply lt_O_Sn.
case => Hx1.
rewrite Hval /plus /scal /= /mult /=.
replace (_-_) with (c * (b - SF_h ptd) - Riemann_sum phi ptd) by ring.
by apply IH.
split.
apply Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
apply Rle_lt_trans with (2 := Hx1), (Hptd O (lt_O_Sn _)).
rewrite Hx1 Riemann_sum_zero.
change zero with 0.
rewrite /plus /scal /= /mult /=.
replace (_ - _) with ((c - phi y0) * (b - x0)) by ring.
apply Rle_trans with ((fmax - fmin) * alpha).
rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
suff : a <= y0 <= b.
case ; case => Ha'.
case => Hb'.
rewrite Hval.
rewrite Rminus_eq_0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ; case: Rle_dec => // H0 H1 H2.
by apply Rlt_le, Rnot_le_lt, H1.
by apply Rle_refl.
by apply Rlt_le, Rnot_le_lt, H0.
by apply Rle_refl.
by apply Rlt_le, Rnot_le_lt, H0.
by split.
rewrite Hb' ; apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ; apply Rplus_le_compat, Ropp_le_contravar.
by apply Rmin_r.
by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
by apply RmaxLess2.
by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
rewrite -Ha' => _ ; apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ; apply Rplus_le_compat, Ropp_le_contravar.
by apply Rmin_r.
by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
by apply RmaxLess2.
by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
split.
apply Rlt_le, Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
apply Rle_trans with (SF_h ptd).
apply (Hptd O (lt_O_Sn _)).
by apply Req_le.
apply Rlt_le, Rle_lt_trans with (2 := Hstep) ; rewrite /seq_step /= -Hx1 ; apply RmaxLess1.
rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
apply Req_le ; field.
by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
apply Rlt_le, eps2.
apply H.
apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
by rewrite /SF_lx /= Hb.
rewrite Hx0 Riemann_sum_zero.
change zero with 0.
replace (c * (b - b) - 0) with 0 by ring.
rewrite Rabs_R0 ; apply Rlt_le, eps2.
apply ptd_sort, Hptd.
by rewrite /SF_lx /= Hb.
rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
apply ptd_sort, Hptd.
apply lt_O_Sn.
rewrite Riemann_sum_cons /= -Ha.
rewrite Rminus_eq_0 scal_zero_l plus_zero_l.
Admitted.

Lemma ex_RInt_Reals_1 (f : R -> R) (a b : R) : Riemann_integrable f a b -> ex_RInt f a b.
Proof.
move => pr ; exists (RiemannInt pr).
Admitted.

Lemma ex_RInt_Reals_0 (f : R -> R) (a b : R) : ex_RInt f a b -> Riemann_integrable f a b.
Admitted.

Lemma RInt_Reals (f : R -> R) (a b : R) : forall pr, RInt f a b = @RiemannInt f a b pr.
Proof.
intros pr.
apply is_RInt_unique.
Admitted.

Lemma ex_RInt_norm : forall (f : R -> R) a b, ex_RInt f a b -> ex_RInt (fun x => norm (f x)) a b.
Proof.
intros f a b If.
apply ex_RInt_Reals_1.
apply RiemannInt_P16.
Admitted.

Lemma abs_RInt_le : forall (f : R -> R) a b, a <= b -> ex_RInt f a b -> Rabs (RInt f a b) <= RInt (fun t => Rabs (f t)) a b.
Proof.
intros f a b H1 If.
apply: (norm_RInt_le f (fun t : R => norm (f t)) a b).
exact H1.
move => x _ ; by apply Rle_refl.
exact: RInt_correct.
apply: RInt_correct.
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
by apply Cf.
