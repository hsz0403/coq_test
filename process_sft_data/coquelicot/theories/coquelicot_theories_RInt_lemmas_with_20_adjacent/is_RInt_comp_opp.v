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

Lemma is_RInt_point : forall (f : R -> V) (a : R), is_RInt f a a zero.
Proof.
intros f a.
apply filterlim_locally.
move => eps ; exists (mkposreal _ Rlt_0_1) => ptd _ [Hptd [Hh Hl]].
rewrite Riemann_sum_zero.
rewrite scal_zero_r.
by apply ball_center.
by apply ptd_sort.
Admitted.

Lemma ex_RInt_point : forall (f : R -> V) a, ex_RInt f a a.
Proof.
intros f a.
Admitted.

Lemma is_RInt_swap : forall (f : R -> V) (a b : R) (If : V), is_RInt f b a If -> is_RInt f a b (opp If).
Proof.
unfold is_RInt.
intros f a b If HIf.
rewrite -scal_opp_one /=.
apply filterlim_ext with (fun ptd => scal (opp (one : R)) (scal (sign (a - b)) (Riemann_sum f ptd))).
intros x.
rewrite scal_assoc.
apply (f_equal (fun s => scal s _)).
rewrite /mult /opp /one /=.
by rewrite -(Ropp_minus_distr' b a) sign_opp /= Ropp_mult_distr_l_reverse Rmult_1_l.
unfold Riemann_fine.
rewrite Rmin_comm Rmax_comm.
apply filterlim_comp with (1 := HIf).
Admitted.

Lemma ex_RInt_swap : forall (f : R -> V) (a b : R), ex_RInt f a b -> ex_RInt f b a.
Proof.
intros f a b.
case => If HIf.
exists (opp If).
Admitted.

Lemma ex_RInt_ub (f : R -> V) (a b : R) : ex_RInt f a b -> exists M : R, forall t : R, Rmin a b <= t <= Rmax a b -> norm (f t) <= M.
Admitted.

Lemma is_RInt_ext : forall (f g : R -> V) (a b : R) (l : V), (forall x, Rmin a b < x < Rmax a b -> f x = g x) -> is_RInt f a b l -> is_RInt g a b l.
Proof.
intros f g a b.
wlog: a b / (a < b) => [Hw | Hab] l Heq Hf.
case: (Rle_lt_dec a b) => Hab.
case: Hab => Hab.
by apply Hw.
rewrite -Hab in Hf |- *.
move: Hf ; apply filterlim_ext => x.
by rewrite Rminus_eq_0 sign_0 !scal_zero_l.
rewrite -(opp_opp l).
apply is_RInt_swap.
apply Hw.
by [].
by rewrite Rmin_comm Rmax_comm.
by apply is_RInt_swap.
move: Heq ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Heq.
apply filterlim_locally_ball_norm => eps.
destruct (proj1 (filterlim_locally_ball_norm _ _) Hf (pos_div_2 eps)) as [d Hd].
set dx := fun x => pos_div_2 (pos_div_2 eps) / Rmax 1 (norm (minus (g x) (f x))).
assert (forall x, 0 < dx x).
intros x.
apply Rdiv_lt_0_compat.
apply is_pos_div_2.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
assert (Hdelta : 0 < Rmin d (Rmin (dx a) (dx b))).
repeat apply Rmin_case => //.
by apply d.
exists (mkposreal _ Hdelta) => /= y Hstep [Hptd [Hya Hyb]].
rewrite (double_var eps).
eapply ball_norm_triangle.
apply Hd.
eapply Rlt_le_trans, Rmin_l.
by apply Hstep.
split => //.
have: (seq_step (SF_lx y) < (Rmin (dx a) (dx b))) => [ | {Hstep} Hstep].
eapply Rlt_le_trans, Rmin_r.
by apply Hstep.
clear d Hd Hdelta Hf.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite !scal_one.
move: Hya Hyb ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Hya Hyb.
move: Hab Heq Hstep ; rewrite -Hyb => {b Hyb} ; set b := last (SF_h y) (unzip1 (SF_t y)) ; rewrite -Hya => {a Hya} ; set a := SF_h y => Hab Heq Hstep.
revert a b Hab Heq Hptd Hstep ; apply SF_cons_ind with (s := y) => {y} [x0 | x0 y IH] a b Hab Heq Hptd Hstep.
rewrite !Riemann_sum_zero //.
by apply (ball_norm_center _ (pos_div_2 eps)).
rewrite !Riemann_sum_cons.
assert (Hx0 := proj1 (ptd_sort _ Hptd)).
case: Hx0 => /= Hx0.
Focus 2.
rewrite Hx0 Rminus_eq_0 !scal_zero_l !plus_zero_l.
apply: IH.
move: Hab ; unfold a, b ; simpl ; by rewrite Hx0.
intros x Hx.
apply Heq ; split.
unfold a ; simpl ; rewrite Hx0 ; apply Hx.
unfold b ; simpl ; apply Hx.
eapply ptd_cons, Hptd.
move: Hstep ; unfold a, b ; simpl ; rewrite Hx0.
apply Rle_lt_trans, Rmax_r.
clear IH.
rewrite (double_var (eps / 2)).
eapply Rle_lt_trans, Rplus_lt_compat.
eapply Rle_trans, norm_triangle.
apply Req_le, f_equal.
replace (@minus V _ _) with (plus (scal (SF_h y - fst x0) (minus (g (snd x0)) (f (snd x0)))) (minus (Riemann_sum g y) (Riemann_sum f y))).
by [].
rewrite /minus opp_plus scal_distr_l -scal_opp_r -!plus_assoc.
apply f_equal.
rewrite !plus_assoc ; apply f_equal2 => //.
by apply plus_comm.
eapply Rle_lt_trans.
apply @norm_scal.
assert (Ha := proj1 (Hptd O (lt_O_Sn _))).
case: Ha => /= Ha.
assert (Hb : snd x0 <= b).
eapply Rle_trans, sorted_last.
2: apply ptd_sort.
2: eapply ptd_cons, Hptd.
2: apply lt_O_Sn.
simpl.
apply (Hptd O), lt_O_Sn.
case: Hb => //= Hb.
rewrite Heq.
rewrite minus_eq_zero norm_zero Rmult_0_r.
apply (is_pos_div_2 (pos_div_2 eps)).
by split.
rewrite Hb.
eapply Rle_lt_trans.
apply Rmult_le_compat_l, (Rmax_r 1).
by apply abs_ge_0.
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
rewrite -/(dx b).
eapply Rlt_le_trans, Rmin_r.
eapply Rle_lt_trans, Hstep.
by apply Rmax_l.
rewrite -Ha.
eapply Rle_lt_trans.
apply Rmult_le_compat_l, (Rmax_r 1).
by apply abs_ge_0.
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
rewrite -/(dx a).
eapply Rlt_le_trans, Rmin_l.
eapply Rle_lt_trans, Hstep.
by apply Rmax_l.
have: (forall x : R, SF_h y <= x < b -> f x = g x) => [ | {Heq} Heq].
intros.
apply Heq ; split.
by eapply Rlt_le_trans, H0.
by apply H0.
have: (seq_step (SF_lx y) < (dx b)) => [ | {Hstep} Hstep].
eapply Rlt_le_trans, Rmin_r.
eapply Rle_lt_trans, Hstep.
apply Rmax_r.
simpl in b.
apply ptd_cons in Hptd.
clear a Hab x0 Hx0.
revert b Heq Hptd Hstep ; apply SF_cons_ind with (s := y) => {y} [x0 | x0 y IH] b Heq Hptd Hstep.
rewrite !Riemann_sum_zero // minus_eq_zero norm_zero.
apply (is_pos_div_2 (pos_div_2 _)).
rewrite !Riemann_sum_cons.
replace (minus (plus (scal (SF_h y - fst x0) (g (snd x0))) (Riemann_sum g y)) (plus (scal (SF_h y - fst x0) (f (snd x0))) (Riemann_sum f y))) with (plus (scal (SF_h y - fst x0) (minus (g (snd x0)) (f (snd x0)))) (minus (Riemann_sum g y) (Riemann_sum f y))).
eapply Rle_lt_trans.
apply @norm_triangle.
assert (SF_h y <= b).
eapply Rle_trans, sorted_last.
2: apply ptd_sort ; eapply ptd_cons, Hptd.
2: apply lt_O_Sn.
simpl ; by apply Rle_refl.
case: H0 => Hb.
rewrite Heq.
rewrite minus_eq_zero scal_zero_r norm_zero Rplus_0_l.
apply IH ; intros.
apply Heq ; split.
eapply Rle_trans, H0.
eapply Rle_trans ; by apply (Hptd O (lt_O_Sn _)).
by apply H0.
eapply ptd_cons, Hptd.
eapply Rle_lt_trans, Hstep.
by apply Rmax_r.
split.
apply (Hptd O (lt_O_Sn _)).
eapply Rle_lt_trans, Hb.
apply (Hptd O (lt_O_Sn _)).
clear IH.
rewrite Hb !Riemann_sum_zero //.
rewrite minus_eq_zero norm_zero Rplus_0_r.
eapply Rle_lt_trans.
apply @norm_scal.
assert (snd x0 <= b).
rewrite -Hb.
apply (Hptd O (lt_O_Sn _)).
case: H0 => Hb'.
rewrite Heq.
rewrite minus_eq_zero norm_zero Rmult_0_r.
apply (is_pos_div_2 (pos_div_2 _)).
split.
apply (Hptd O (lt_O_Sn _)).
by [].
rewrite Hb'.
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
apply abs_ge_0.
apply (Rmax_r 1).
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
eapply Rle_lt_trans, Hstep.
rewrite -Hb.
by apply Rmax_l.
apply ptd_sort ; eapply ptd_cons, Hptd.
apply ptd_sort ; eapply ptd_cons, Hptd.
rewrite /minus opp_plus scal_distr_l -scal_opp_r -!plus_assoc.
apply f_equal.
rewrite !plus_assoc.
apply f_equal2 => //.
Admitted.

Lemma ex_RInt_ext : forall (f g : R -> V) (a b : R), (forall x, Rmin a b < x < Rmax a b -> f x = g x) -> ex_RInt f a b -> ex_RInt g a b.
Proof.
intros f g a b Heq [If Hex].
exists If.
revert Hex.
Admitted.

Lemma is_RInt_const : forall (a b : R) (v : V), is_RInt (fun _ => v) a b (scal (b - a) v).
Proof.
intros a b v.
apply filterlim_within_ext with (fun _ => scal (b - a) v).
2: apply filterlim_const.
intros ptd [_ [Hhead Hlast]].
rewrite Riemann_sum_const.
rewrite Hlast Hhead.
rewrite scal_assoc.
apply (f_equal (fun x => scal x v)).
Admitted.

Lemma ex_RInt_const : forall (a b : R) (v : V), ex_RInt (fun _ => v) a b.
Proof.
intros a b v.
exists (scal (b - a) v).
Admitted.

Lemma ex_RInt_comp_opp : forall (f : R -> V) (a b : R), ex_RInt f (-a) (-b) -> ex_RInt (fun y => opp (f (- y))) a b.
Proof.
intros f a b [l If].
exists l.
Admitted.

Lemma is_RInt_comp_lin (f : R -> V) (u v a b : R) (l : V) : is_RInt f (u * a + v) (u * b + v) l -> is_RInt (fun y => scal u (f (u * y + v))) a b l.
Proof.
case: (Req_dec u 0) => [-> {u} If | ].
evar_last.
apply is_RInt_ext with (fun _ => zero).
move => x _ ; apply sym_eq ; apply: scal_zero_l.
apply is_RInt_const.
apply filterlim_locally_unique with (2 := If).
rewrite !Rmult_0_l Rplus_0_l.
rewrite scal_zero_r.
apply is_RInt_point.
wlog: u a b / (u > 0) => [Hw | Hu _].
case: (Rlt_le_dec 0 u) => Hu.
by apply Hw.
case: Hu => // Hu _ If.
apply is_RInt_ext with (fun y => opp (scal (- u) (f ((- u) * (- y) + v)))).
move => x _.
rewrite -(scal_opp_l (- u) (f (- u * - x + v))) /=.
rewrite /opp /= Ropp_involutive.
apply f_equal.
apply f_equal ; ring.
apply (is_RInt_comp_opp (fun y => scal (- u) (f (- u * y + v)))).
apply Hw.
by apply Ropp_gt_lt_0_contravar.
by apply Ropp_neq_0_compat, Rlt_not_eq.
by rewrite ?Rmult_opp_opp.
wlog: a b l / (a < b) => [Hw | Hab].
case: (Rlt_le_dec a b) => Hab If.
by apply Hw.
case: Hab If => [Hab | -> {b}] If.
rewrite -(opp_opp l).
apply is_RInt_swap.
apply Hw.
by [].
by apply is_RInt_swap.
evar_last.
apply is_RInt_point.
apply filterlim_locally_unique with (2 := If).
apply is_RInt_point.
intros If.
apply filterlim_locally.
generalize (proj1 (filterlim_locally _ l) If).
move => {If} If eps.
case: (If eps) => {If} alpha If.
have Ha : 0 < alpha / Rabs u.
apply Rdiv_lt_0_compat.
by apply alpha.
by apply Rabs_pos_lt, Rgt_not_eq.
exists (mkposreal _ Ha) => /= ptd Hstep [Hptd [Hfirst Hlast]].
set ptd' := mkSF_seq (u * SF_h ptd + v) (map (fun X => (u * fst X + v,u * snd X + v)) (SF_t ptd)).
replace (scal (sign (b - a)) (Riemann_sum (fun y : R => scal u (f (u * y + v))) ptd)) with (scal (sign (u * b + v - (u * a + v))) (Riemann_sum f ptd')).
apply: If.
revert ptd' ; case: (ptd) Hstep => x0 s Hs /= ; rewrite /seq_step /= in Hs |- *.
elim: s x0 Hs => [ | [x1 y0] s IH] /= x0 Hs.
by apply alpha.
apply Rmax_case.
replace (u * x1 + v - (u * x0 + v)) with (u * (x1 - x0)) by ring.
rewrite Rabs_mult Rmult_comm ; apply Rlt_div_r.
by apply Rabs_pos_lt, Rgt_not_eq.
by apply Rle_lt_trans with (2 := Hs), Rmax_l.
apply IH.
by apply Rle_lt_trans with (2 := Hs), Rmax_r.
split.
revert ptd' ; case: (ptd) Hptd => x0 s Hs /= i Hi ; rewrite /SF_size size_map /= in Hi ; move: (Hs i) => {Hs} Hs ; rewrite /SF_size /= in Hs ; move: (Hs Hi) => {Hs} ; rewrite /SF_lx /SF_ly /= => Hs.
elim: s i x0 Hi Hs => /= [ | [x1 y0] s IH] i x0 Hi Hs.
by apply lt_n_O in Hi.
case: i Hi Hs => /= [ | i] Hi Hs.
split ; apply Rplus_le_compat_r ; apply Rmult_le_compat_l ; try by apply Rlt_le.
by apply Hs.
by apply Hs.
apply IH.
by apply lt_S_n.
by apply Hs.
split.
rewrite /ptd' /= Hfirst.
rewrite -Rplus_min_distr_r.
rewrite -Rmult_min_distr_l.
reflexivity.
by apply Rlt_le.
rewrite -Rplus_max_distr_r.
rewrite -Rmult_max_distr_l.
rewrite -Hlast.
rewrite /ptd' /=.
elim: (SF_t ptd) (SF_h ptd) => [ | [x1 _] /= s IH] x0 //=.
by apply Rlt_le.
apply f_equal2.
replace (u * b + v - (u * a + v)) with (u * (b - a)) by ring.
rewrite sign_mult.
rewrite (sign_eq_1 _ Hu).
apply Rmult_1_l.
revert ptd' ; apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH] //=.
set s' := {| SF_h := u * SF_h s + v; SF_t := [seq (u * fst X + v, u * snd X + v) | X <- SF_t s] |}.
rewrite Riemann_sum_cons (Riemann_sum_cons _ (u * x0 + v,u * y0 + v) s') /=.
rewrite IH.
apply f_equal2 => //=.
rewrite scal_assoc /=.
apply (f_equal (fun x => scal x _)).
Admitted.

Lemma ex_RInt_comp_lin (f : R -> V) (u v a b : R) : ex_RInt f (u * a + v) (u * b + v) -> ex_RInt (fun y => scal u (f (u * y + v))) a b.
Proof.
case => l Hf.
exists l.
Admitted.

Lemma is_RInt_Chasles_0 (f : R -> V) (a b c : R) (l1 l2 : V) : a < b < c -> is_RInt f a b l1 -> is_RInt f b c l2 -> is_RInt f a c (plus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
case: (ex_RInt_ub f a b).
by exists l1.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ M1 HM1.
case: (ex_RInt_ub f b c).
by exists l2.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ M2 HM2.
apply filterlim_locally_ball_norm => eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 (pos_div_2 eps))) => {H1} H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 (pos_div_2 eps))) => {H2} H2.
case: H1 => d1 H1.
case: H2 => d2 H2.
move: H1 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ H1.
move: H2 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ H2.
have Hd3 : 0 < eps / (4 * ((M1 + 1) + (M2 + 1))).
apply Rdiv_lt_0_compat.
by apply eps.
repeat apply Rmult_lt_0_compat.
by apply Rlt_0_2.
by apply Rlt_0_2.
apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
apply Rle_trans with (2 := HM1), norm_ge_0.
specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
apply Rle_trans with (2 := HM2), norm_ge_0.
have Hd : 0 < Rmin (Rmin d1 d2) (mkposreal _ Hd3).
repeat apply Rmin_case.
by apply d1.
by apply d2.
by apply Hd3.
exists (mkposreal _ Hd) => /= ptd Hstep [Hptd [Hh Hl]].
move: Hh Hl ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => //= _ _ Hh Hl.
rewrite -> sign_eq_1 by now apply Rlt_Rminus, Rlt_trans with b.
rewrite scal_one.
rewrite /ball_norm (double_var eps).
apply Rle_lt_trans with (norm (minus (Riemann_sum f ptd) (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b)))) + norm (minus (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))).
set v:= minus _ (plus l1 l2).
replace v with (plus (minus (Riemann_sum f ptd) (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b)))) (minus (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))).
exact: norm_triangle.
rewrite /v /minus -plus_assoc.
apply f_equal.
by rewrite plus_assoc plus_opp_l plus_zero_l.
apply Rplus_lt_compat.
apply Rlt_le_trans with (2 := Rmin_r _ _) in Hstep.
generalize (fun H H0 => Riemann_sum_Chasles_0 f (M1 + 1 + (M2 + 1)) b ptd (mkposreal _ Hd3) H H0 Hptd Hstep).
rewrite /= Hl Hh => H.
replace (eps / 2) with (2 * (mkposreal _ Hd3) * (M1 + 1 + (M2 + 1))).
rewrite -norm_opp opp_plus opp_opp plus_comm.
simpl ; apply H.
intros x Hx.
case: (Rle_lt_dec x b) => Hxb.
apply Rlt_trans with (M1 + 1).
apply Rle_lt_trans with M1.
apply HM1 ; split.
by apply Hx.
by apply Hxb.
apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
apply Rminus_lt_0 ; ring_simplify.
apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
apply Rle_trans with (2 := HM2), norm_ge_0.
apply Rlt_trans with (M2 + 1).
apply Rle_lt_trans with M2.
apply HM2 ; split.
by apply Rlt_le, Hxb.
by apply Hx.
apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
apply Rminus_lt_0 ; ring_simplify.
apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
apply Rle_trans with (2 := HM1), norm_ge_0.
split ; by apply Rlt_le.
simpl ; field.
apply Rgt_not_eq.
apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
apply Rle_trans with (2 := HM1), norm_ge_0.
specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
apply Rle_trans with (2 := HM2), norm_ge_0.
apply Rlt_le_trans with (2 := Rmin_l _ _) in Hstep.
specialize (H1 (SF_cut_down ptd b)).
specialize (H2 (SF_cut_up ptd b)).
apply Rle_lt_trans with (norm (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1) + norm (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
replace (minus (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2)) with (plus (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1) (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
apply @norm_triangle.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite 2!scal_one /minus opp_plus -2!plus_assoc.
apply f_equal.
rewrite plus_comm -plus_assoc.
apply f_equal.
by apply plus_comm.
rewrite (double_var (eps / 2)) ; apply Rplus_lt_compat.
apply H1.
apply SF_cut_down_step.
rewrite /= Hl Hh ; split ; by apply Rlt_le.
by apply Rlt_le_trans with (1 := Hstep), Rmin_l.
split.
apply SF_cut_down_pointed.
rewrite Hh ; by apply Rlt_le.
by [].
split.
rewrite SF_cut_down_h.
by apply Hh.
rewrite Hh ; by apply Rlt_le.
move: (SF_cut_down_l ptd b) => //=.
apply H2.
apply SF_cut_up_step.
rewrite /= Hl Hh ; split ; by apply Rlt_le.
by apply Rlt_le_trans with (1 := Hstep), Rmin_r.
split.
apply SF_cut_up_pointed.
rewrite Hh ; by apply Rlt_le.
by [].
split.
by rewrite SF_cut_up_h.
move: (SF_cut_up_l ptd b) => /= ->.
by apply Hl.
Admitted.

Lemma ex_RInt_Chasles_0 (f : R -> V) (a b c : R) : a <= b <= c -> ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
case => Hab Hbc H1 H2.
case: Hab => [ Hab | -> ] //.
case: Hbc => [ Hbc | <- ] //.
case: H1 => [l1 H1] ; case: H2 => [l2 H2].
exists (plus l1 l2).
apply is_RInt_Chasles_0 with b ; try assumption.
Admitted.

Lemma is_RInt_Chasles_1 (f : R -> V) (a b c : R) l1 l2 : a < b < c -> is_RInt f a c l1 -> is_RInt f b c l2 -> is_RInt f a b (minus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
apply filterlim_locally_ball_norm => eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => {H1} d1 /= H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => {H2} d2 /= H2.
exists d1 ; simpl ; intros y Hstep [Hptd [Hh Hl]].
assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\ pointed_subdiv y /\ SF_h y = Rmin b c /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax b c).
apply filter_ex.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
repeat (split => //=).
by apply H5.
by apply H6.
case: H => y2 [Hstep2 H].
specialize (H2 y2 (Rlt_le_trans _ _ _ Hstep2 (Rmin_r _ _)) H).
case: H => Hptd2 [Hh2 Hl2].
set y1 := mkSF_seq (SF_h y) (SF_t y ++ SF_t y2).
move: Hl Hh2 Hh Hl2 H1 H2 ; rewrite /Rmax /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) (Rlt_le _ _ Hbc) => // _ _ ; case: Rle_dec => // _ _.
case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => // _ _.
move => Hl Hh2 Hh Hl2 H1 H2.
rewrite -Hl in Hab, Hbc, H2, Hh2 |-* => {b Hl}.
rewrite -Hh in H1, Hab |- * => {a Hh}.
rewrite -Hl2 in Hbc, H2, H1 => {c Hl2}.
assert (seq_step (SF_lx y1) < d1).
unfold y1 ; move: Hstep Hh2.
clear -Hstep2.
apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hstep Hl.
rewrite -Hl.
by apply Rlt_le_trans with (1 := Hstep2), Rmin_l.
rewrite /SF_lx /seq_step /= in Hstep |- * ; move: (Rle_lt_trans _ _ _ (Rmax_r _ _) Hstep) (Rle_lt_trans _ _ _ (Rmax_l _ _) Hstep) => {Hstep} /= H H0.
apply Rmax_case.
by [].
by apply IH.
assert (pointed_subdiv y1 /\ SF_h y1 = SF_h y /\ last (SF_h y1) (unzip1 (SF_t y1)) = last (SF_h y2) (unzip1 (SF_t y2))).
split.
unfold y1 ; move: Hptd Hh2.
clear -Hptd2.
apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hptd Hl.
rewrite -Hl ; by apply Hptd2.
case => [ | i] /= Hi.
by apply (Hptd O (lt_O_Sn _)).
apply (IH (ptd_cons _ _ Hptd) Hl i (lt_S_n _ _ Hi)).
unfold y1 ; simpl ; split.
by [].
move: Hh2 ; clear ; apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
by rewrite Hl.
by apply IH.
specialize (H1 y1 H H0).
move: Hab Hbc Hh2 H1 H2 ; clear ; set c := last (SF_h y2) (unzip1 (SF_t y2)) ; set b := last (SF_h y) (unzip1 (SF_t y)) ; set a := SF_h y => Hab Hbc Hl.
rewrite -> sign_eq_1 by now apply Rlt_Rminus, Rlt_trans with b.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite 3!scal_one.
replace (Riemann_sum f y) with (minus (Riemann_sum f y1) (Riemann_sum f y2)).
move => H1 H2.
unfold ball_norm.
set v := minus _ _.
replace v with (minus (minus (Riemann_sum f y1) l1) (minus (Riemann_sum f y2) l2)).
rewrite (double_var eps).
apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
rewrite -(norm_opp (minus (Riemann_sum f y2) l2)).
by apply @norm_triangle.
rewrite /v /minus 2!opp_plus opp_opp 2!plus_assoc.
apply (f_equal (fun x => plus x _)).
rewrite -!plus_assoc.
apply f_equal.
by apply plus_comm.
move: Hl ; unfold y1, b.
clear.
apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
by rewrite -Hl /minus plus_opp_r.
rewrite (Riemann_sum_cons _ (x0,y0) {| SF_h := SF_h y; SF_t := SF_t y ++ SF_t y2 |}) /=.
rewrite Riemann_sum_cons /=.
rewrite /minus -plus_assoc.
apply f_equal.
Admitted.

Lemma is_RInt_Chasles_2 (f : R -> V) (a b c : R) l1 l2 : a < b < c -> is_RInt f a c l1 -> is_RInt f a b l2 -> is_RInt f b c (minus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
rewrite -(Ropp_involutive a) -(Ropp_involutive b) -(Ropp_involutive c) in H1 H2.
apply is_RInt_comp_opp, is_RInt_swap in H1.
apply is_RInt_comp_opp, is_RInt_swap in H2.
apply Ropp_lt_contravar in Hab.
apply Ropp_lt_contravar in Hbc.
generalize (is_RInt_Chasles_1 _ _ _ _ _ _ (conj Hbc Hab) H1 H2).
clear => H.
apply is_RInt_comp_opp, is_RInt_swap in H.
replace (minus l1 l2) with (opp (minus (opp l1) (opp l2))).
move: H ; apply is_RInt_ext.
now move => x _ ; rewrite opp_opp Ropp_involutive.
Admitted.

Lemma is_RInt_Chasles (f : R -> V) (a b c : R) (l1 l2 : V) : is_RInt f a b l1 -> is_RInt f b c l2 -> is_RInt f a c (plus l1 l2).
Proof.
wlog: a c l1 l2 / (a <= c) => [Hw | Hac].
move => H1 H2.
case: (Rle_lt_dec a c) => Hac.
by apply Hw.
rewrite -(opp_opp (plus _ _)) opp_plus plus_comm.
apply is_RInt_swap.
apply Hw.
by apply Rlt_le.
by apply is_RInt_swap.
by apply is_RInt_swap.
case: (Req_dec a b) => [ <- {b} | Hab'] H1.
-
move => H2.
apply filterlim_locally_ball_norm => /= eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
assert (pointed_subdiv (SF_nil a) /\ SF_h (SF_nil (T := V) a) = Rmin a a /\ last (SF_h (SF_nil (T := V) a)) (unzip1 (SF_t (SF_nil (T := V) a))) = Rmax a a).
split.
move => i Hi ; by apply lt_n_O in Hi.
rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl a).
specialize (H1 (SF_nil a) (cond_pos d1) H) => {H d1}.
rewrite Rminus_eq_0 sign_0 in H1.
assert (H := scal_zero_l (Riemann_sum f (SF_nil a))).
rewrite /ball_norm H /minus plus_zero_l in H1 => {H}.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
exists d2 => ptd Hstep Hptd.
apply Rle_lt_trans with (norm (minus (scal (sign (c - a)) (Riemann_sum f ptd)) l2) + norm (opp l1)).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
rewrite /minus opp_plus -plus_assoc.
by apply f_equal, @plus_comm.
rewrite (double_var eps) ; apply Rplus_lt_compat.
by apply H2.
by apply H1.
case: (Req_dec b c) => [ <- | Hbc'] H2.
-
apply filterlim_locally_ball_norm => /= eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
assert (pointed_subdiv (SF_nil b) /\ SF_h (SF_nil (T := V) b) = Rmin b b /\ last (SF_h (SF_nil (T := V) b)) (unzip1 (SF_t (SF_nil (T := V) b))) = Rmax b b).
split.
move => i Hi ; by apply lt_n_O in Hi.
rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl b).
specialize (H2 (SF_nil b) (cond_pos d2) H) => {H d2}.
rewrite Rminus_eq_0 sign_0 in H2.
assert (H := scal_zero_l (Riemann_sum f (SF_nil a))).
rewrite /ball_norm H /minus plus_zero_l in H2 => {H}.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
exists d1 => ptd Hstep Hptd.
apply Rle_lt_trans with (norm (minus (scal (sign (b - a)) (Riemann_sum f ptd)) l1) + norm (opp l2)).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
by rewrite /minus opp_plus -plus_assoc.
rewrite (double_var eps) ; apply Rplus_lt_compat.
by apply H1.
by apply H2.
case: (Req_dec a c) => Hac'.
-
rewrite -Hac' in H1 Hbc' H2 Hac |- * => {c Hac'}.
apply is_RInt_swap in H2.
apply filterlim_locally_ball_norm => /= eps.
exists (mkposreal _ Rlt_0_1) => y Hstep Hy.
rewrite Rminus_eq_0 sign_0.
assert (H := scal_zero_l (Riemann_sum f y)).
rewrite /ball_norm H /minus plus_zero_l opp_plus => {H y Hstep Hy}.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\ pointed_subdiv y /\ SF_h y = Rmin a b /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax a b).
apply filter_ex.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
repeat (split => //=).
by apply H5.
by apply H6.
case: H => y [Hstep Hy].
specialize (H1 _ (Rlt_le_trans _ _ _ Hstep (Rmin_l _ _)) Hy).
specialize (H2 _ (Rlt_le_trans _ _ _ Hstep (Rmin_r _ _)) Hy).
rewrite (double_var eps).
rewrite /ball_norm -norm_opp /minus opp_plus opp_opp in H2.
apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
rewrite plus_assoc /minus.
apply (f_equal (fun x => plus x _)).
by rewrite plus_comm plus_assoc plus_opp_l plus_zero_l.
case: (Rle_lt_dec a b) => Hab ; try (case: Hab => //= Hab) ; clear Hab' ; case: (Rle_lt_dec b c) => Hbc ; try (case: Hbc => //= Hbc) ; clear Hbc' ; try (case: Hac => //= Hac) ; clear Hac'.
by apply is_RInt_Chasles_0 with b.
apply is_RInt_swap in H2.
rewrite -(opp_opp l2).
by apply is_RInt_Chasles_1 with b.
apply is_RInt_swap in H1.
rewrite -(opp_opp l1) plus_comm.
by apply is_RInt_Chasles_2 with b.
Admitted.

Lemma ex_RInt_Chasles (f : R -> V) (a b c : R) : ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
intros [l1 H1] [l2 H2].
exists (plus l1 l2).
Admitted.

Lemma is_RInt_scal : forall (f : R -> V) (a b : R) (k : R) (If : V), is_RInt f a b If -> is_RInt (fun y => scal k (f y)) a b (scal k If).
Proof.
intros f a b k If Hf.
apply filterlim_ext with (fun ptd => scal k (scal (sign (b - a)) (Riemann_sum f ptd))).
intros ptd.
rewrite Riemann_sum_scal.
rewrite 2!scal_assoc.
apply (f_equal (fun x => scal x _)).
apply Rmult_comm.
apply filterlim_comp with (1 := Hf).
Admitted.

Lemma ex_RInt_scal : forall (f : R -> V) (a b : R) (k : R), ex_RInt f a b -> ex_RInt (fun y => scal k (f y)) a b.
Proof.
intros f a b k [If Hf].
exists (scal k If).
Admitted.

Lemma is_RInt_opp : forall (f : R -> V) (a b : R) (If : V), is_RInt f a b If -> is_RInt (fun y => opp (f y)) a b (opp If).
Proof.
intros f a b If Hf.
apply filterlim_ext with (fun ptd => (scal (opp 1) (scal (sign (b - a)) (Riemann_sum f ptd)))).
intros ptd.
rewrite Riemann_sum_opp.
rewrite scal_opp_one.
apply sym_eq, scal_opp_r.
apply filterlim_comp with (1 := Hf).
rewrite -(scal_opp_one If).
Admitted.

Lemma ex_RInt_opp : forall (f : R -> V) (a b : R), ex_RInt f a b -> ex_RInt (fun x => opp (f x)) a b.
Proof.
intros f a b [If Hf].
exists (opp If).
Admitted.

Lemma is_RInt_plus : forall (f g : R -> V) (a b : R) (If Ig : V), is_RInt f a b If -> is_RInt g a b Ig -> is_RInt (fun y => plus (f y) (g y)) a b (plus If Ig).
Proof.
intros f g a b If Ig Hf Hg.
apply filterlim_ext with (fun ptd => (plus (scal (sign (b - a)) (Riemann_sum f ptd)) (scal (sign (b - a)) (Riemann_sum g ptd)))).
intros ptd.
rewrite Riemann_sum_plus.
apply sym_eq, @scal_distr_l.
apply filterlim_comp_2 with (1 := Hf) (2 := Hg).
Admitted.

Lemma ex_RInt_plus : forall (f g : R -> V) (a b : R), ex_RInt f a b -> ex_RInt g a b -> ex_RInt (fun y => plus (f y) (g y)) a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
exists (plus If Ig).
Admitted.

Lemma is_RInt_minus : forall (f g : R -> V) (a b : R) (If Ig : V), is_RInt f a b If -> is_RInt g a b Ig -> is_RInt (fun y => minus (f y) (g y)) a b (minus If Ig).
Proof.
intros f g a b If Ig Hf Hg.
apply filterlim_ext with (fun ptd => (plus (scal (sign (b - a)) (Riemann_sum f ptd)) (scal (opp 1) (scal (sign (b - a)) (Riemann_sum g ptd))))).
intros ptd.
rewrite Riemann_sum_minus.
unfold minus.
rewrite scal_opp_one.
rewrite -scal_opp_r.
apply sym_eq, @scal_distr_l.
eapply filterlim_comp_2 with (1 := Hf).
apply filterlim_comp with (1 := Hg).
eapply @filterlim_scal_r.
rewrite scal_opp_one.
Admitted.

Lemma ex_RInt_minus : forall (f g : R -> V) (a b : R), ex_RInt f a b -> ex_RInt g a b -> ex_RInt (fun y => minus (f y) (g y)) a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
exists (minus If Ig).
Admitted.

Lemma ex_RInt_Chasles_1 {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b c : R) : a <= b <= c -> ex_RInt f a c -> ex_RInt f a b.
Proof.
intros [Hab Hbc] If.
case: Hab => [Hab | <- ].
2: by apply ex_RInt_point.
assert (H1 := filterlim_locally_cauchy (F := (Riemann_fine a b)) (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum f ptd))).
apply H1 ; clear H1.
intros eps.
set (M := @norm_factor _ V).
assert (He : 0 < eps / M).
apply Rdiv_lt_0_compat.
apply cond_pos.
apply norm_factor_gt_0.
assert (H1 := proj2 (filterlim_locally_cauchy (F := (Riemann_fine a c)) (fun ptd : SF_seq => scal (sign (c - a)) (Riemann_sum f ptd)))).
destruct (H1 If (mkposreal _ He)) as [P [[alpha HP] H2]] ; clear If H1 ; rename H2 into If.
destruct (filter_ex (F := Riemann_fine b c) (fun y => seq_step (SF_lx y) < alpha /\ pointed_subdiv y /\ SF_h y = Rmin b c /\ seq.last (SF_h y) (SF_lx y) = Rmax b c)) as [y' Hy'].
by exists alpha.
exists (fun y => P (SF_cat y y') /\ last (SF_h y) (SF_lx y) = Rmax a b) ; split.
exists alpha ; intros.
assert (last 0 (SF_lx y) = head 0 (SF_lx y')).
simpl in H0, Hy' |- *.
rewrite (proj1 (proj2 (proj2 Hy'))).
rewrite (proj2 (proj2 H0)).
rewrite /Rmin ; case: Rle_dec => // _.
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //.
split.
apply HP ; intuition.
rewrite SF_lx_cat seq_step_cat.
by apply Rmax_case.
by apply lt_O_Sn.
by apply lt_O_Sn.
by [].
apply SF_cat_pointed => //.
rewrite H3 /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
case: Rle_dec (Rlt_le _ _ (Rlt_le_trans _ _ _ Hab Hbc)) => //.
rewrite SF_last_cat // H8.
rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
case: Rle_dec (Rlt_le _ _ (Rlt_le_trans _ _ _ Hab Hbc)) => //.
by apply H0.
intros.
specialize (If _ _ (proj1 H) (proj1 H0)).
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite -> sign_eq_1 in If by now apply Rlt_Rminus, Rlt_le_trans with b.
apply: norm_compat1.
eapply Rlt_le_trans.
eapply Rle_lt_trans.
2: apply norm_compat2 with (1 := If).
apply Req_le, f_equal.
rewrite !scal_one.
case: H => _ ; case: H0 => _ ; clear ; intros.
rewrite -b1 in b0.
move: v u b0 y' {b1}.
apply (SF_cons_ind (fun v => forall u : SF_seq, last (SF_h v) (SF_lx v) = last (SF_h u) (SF_lx u) -> forall y' : SF_seq, minus (Riemann_sum f v) (Riemann_sum f u) = minus (Riemann_sum f (SF_cat v y')) (Riemann_sum f (SF_cat u y')))) => [v0 | v0 v IH u Huv y].
apply (SF_cons_ind (fun u => last (SF_h (SF_nil v0)) (SF_lx (SF_nil v0)) = last (SF_h u) (SF_lx u) -> forall y' : SF_seq, minus (Riemann_sum f (SF_nil v0)) (Riemann_sum f u) = minus (Riemann_sum f (SF_cat (SF_nil v0) y')) (Riemann_sum f (SF_cat u y')))) => [u0 /= Huv | u0 u IH Huv y].
apply (SF_cons_ind (fun y' : SF_seq => minus (Riemann_sum f (SF_nil v0)) (Riemann_sum f (SF_nil u0)) = minus (Riemann_sum f (SF_cat (SF_nil v0) y')) (Riemann_sum f (SF_cat (SF_nil u0) y')))) => [y0 | y0 y IH].
by [].
simpl in Huv.
rewrite Huv /SF_cat /=.
rewrite (Riemann_sum_cons _ (u0,snd y0)) /=.
rewrite /minus opp_plus (plus_comm (scal _ _)) -plus_assoc.
now rewrite (plus_assoc (scal _ _)) !plus_opp_r plus_zero_l plus_opp_r.
rewrite -SF_cons_cat !Riemann_sum_cons.
rewrite /minus !opp_plus !(plus_comm (opp (scal _ _))) !plus_assoc.
by rewrite -!/(minus _ _) -IH.
rewrite -SF_cons_cat !Riemann_sum_cons.
rewrite /minus -!plus_assoc.
by rewrite -!/(minus _ _) -IH.
fold M.
apply Req_le ; simpl ; field.
Admitted.

Lemma ex_RInt_Chasles_2 {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b c : R) : a <= b <= c -> ex_RInt f a c -> ex_RInt f b c.
Proof.
intros.
rewrite -(Ropp_involutive a) -(Ropp_involutive c) in H0.
apply ex_RInt_comp_opp in H0.
apply ex_RInt_swap in H0.
eapply ex_RInt_Chasles_1 in H0.
apply ex_RInt_comp_opp in H0.
apply ex_RInt_swap in H0.
move: H0 ; apply ex_RInt_ext => x _.
by rewrite opp_opp Ropp_involutive.
Admitted.

Lemma ex_RInt_inside {V : CompleteNormedModule R_AbsRing} : forall (f : R -> V) (a b x e : R), ex_RInt f (x-e) (x+e) -> Rabs (a-x) <= e -> Rabs (b-x) <= e -> ex_RInt f a b.
Proof.
intros f a b x e Hf Ha Hb.
wlog: a b Ha Hb / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
now left.
apply (ex_RInt_Chasles_1 f a b) with (x+e).
split.
exact Hab.
assert (x-e <= b <= x+e) by now apply Rabs_le_between'.
apply H.
apply ex_RInt_Chasles_2 with (x-e).
now apply Rabs_le_between'.
Admitted.

Lemma is_RInt_comp_opp : forall (f : R -> V) (a b : R) (l : V), is_RInt f (-a) (-b) l -> is_RInt (fun y => opp (f (- y))) a b l.
Proof.
intros f a b l Hf.
apply filterlim_locally => eps.
generalize (proj1 (filterlim_locally _ _) Hf eps) ; clear Hf ; intros [delta Hf].
exists delta.
intros ptd Hstep [Hptd [Hh Hl]].
rewrite Riemann_sum_opp.
rewrite scal_opp_r -scal_opp_l /opp /= -sign_opp.
rewrite Ropp_plus_distr.
set ptd' := (mkSF_seq (-SF_h ptd) (seq.map (fun X => (- fst X,- snd X)) (SF_t ptd))).
replace (Riemann_sum (fun x => f (-x)) ptd) with (Riemann_sum f (SF_rev ptd')).
have H : SF_size ptd = SF_size ptd'.
rewrite /SF_size /=.
by rewrite size_map.
apply Hf.
clear H ; revert ptd' Hstep ; apply SF_cons_dec with (s := ptd) => [ x0 s' Hs'| h0 s] ; rewrite /seq_step.
apply cond_pos.
set s' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_rev_cons (-fst h0,-snd h0) s').
rewrite SF_lx_rcons.
rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
rewrite head_rcons.
rewrite SF_lx_cons.
revert h0 s' ; move: {1 3}(0) ; apply SF_cons_ind with (s := s) => {s} [ x1 | h1 s IH] x0 h0 s' Hs' ; simpl in Hs'.
rewrite /= -Ropp_minus_distr' /Rminus -Ropp_plus_distr Ropp_involutive.
by apply Hs'.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_rev_cons (-fst h1,-snd h1) s'').
rewrite SF_lx_rcons.
rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
rewrite head_rcons.
rewrite pairmap_rcons.
rewrite foldr_rcons.
apply: IH => /=.
replace (Rmax (Rabs (SF_h s - fst h1)) (foldr Rmax (Rmax (Rabs (- fst h0 - - fst h1)) x0) (pairmap (fun x y : R => Rabs (y - x)) (SF_h s) (unzip1 (SF_t s))))) with (Rmax (Rabs (fst h1 - fst h0)) (Rmax (Rabs (SF_h s - fst h1)) (foldr Rmax x0 (pairmap (fun x y : R => Rabs (y - x)) (SF_h s) (unzip1 (SF_t s)))))).
by [].
rewrite Rmax_assoc (Rmax_comm (Rabs _)) -Rmax_assoc.
apply f_equal.
rewrite -(Ropp_minus_distr' (-fst h0)) /Rminus -Ropp_plus_distr Ropp_involutive.
elim: (pairmap (fun x y : R => Rabs (y + - x)) (SF_h s) (unzip1 (SF_t s))) x0 {Hs'} (Rabs (fst h1 + - fst h0)) => [ | x2 t IH] x0 x1 /=.
by [].
rewrite Rmax_assoc (Rmax_comm x1) -Rmax_assoc.
apply f_equal.
by apply IH.
split.
revert ptd' Hptd H ; apply SF_cons_ind with (s := ptd) => [ x0 | h0 s IH] s' Hs' H i Hi ; rewrite SF_size_rev -H in Hi.
by apply lt_n_O in Hi.
rewrite SF_size_cons in Hi.
apply lt_n_Sm_le in Hi.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_rev_cons (-fst h0,-snd h0) s'').
rewrite SF_size_cons (SF_size_cons (-fst h0,-snd h0) s'') in H.
apply eq_add_S in H.
rewrite SF_lx_rcons SF_ly_rcons.
rewrite ?nth_rcons.
rewrite ?SF_size_lx ?SF_size_ly ?SF_size_rev -H.
move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ; case: (ssrnat.leq (S i) (S (SF_size s))) => // _.
apply le_lt_eq_dec in Hi ; case: Hi => [Hi | -> {i}].
apply lt_le_S in Hi.
move: (proj2 (SSR_leq _ _) Hi) ; case: (ssrnat.leq (S i) (SF_size s)) => // _.
move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ; case: (ssrnat.leq (S (S i)) (S (SF_size s))) => // _.
apply IH.
move: Hs' ; apply ptd_cons.
apply H.
rewrite SF_size_rev -H.
intuition.
have : ~ is_true (ssrnat.leq (S (SF_size s)) (SF_size s)).
have H0 := lt_n_Sn (SF_size s).
contradict H0.
apply SSR_leq in H0.
by apply le_not_lt.
case: (ssrnat.leq (S (SF_size s)) (SF_size s)) => // _.
move: (@eqtype.eq_refl ssrnat.nat_eqType (SF_size s)) ; case: (@eqtype.eq_op ssrnat.nat_eqType (SF_size s) (SF_size s)) => // _.
have : ~ is_true (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))).
have H0 := lt_n_Sn (SF_size s).
contradict H0.
apply SSR_leq in H0.
by apply le_not_lt, le_S_n.
case: (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))) => // _.
move: (@eqtype.eq_refl ssrnat.nat_eqType (S (SF_size s))) ; case: (@eqtype.eq_op ssrnat.nat_eqType (S (SF_size s)) (S (SF_size s))) => // _.
rewrite H SF_lx_rev nth_rev SF_size_lx //=.
replace (ssrnat.subn (S (SF_size s'')) (S (SF_size s''))) with 0%nat by intuition.
simpl.
split ; apply Ropp_le_contravar ; apply (Hs' 0%nat) ; rewrite SF_size_cons ; by apply lt_O_Sn.
split.
rewrite Rmin_opp_Rmax -Hl.
simpl.
clear H.
revert ptd' ; move: (0) ; apply SF_cons_ind with (s := ptd) => [ h0 | h0 s IH] x0 s'.
by simpl.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
rewrite head_rcons.
by apply IH.
rewrite Rmax_opp_Rmin -Hh.
simpl.
clear H.
revert ptd' ; move: (0) ; apply SF_cons_dec with (s := ptd) => [ h0 | h0 s] x0 s'.
by simpl.
set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
rewrite head_rcons.
rewrite behead_rcons ; [ | rewrite size_rev SF_size_lx ; by apply lt_O_Sn].
rewrite unzip1_zip.
by rewrite last_rcons.
rewrite size_rcons size_behead ?size_rev SF_size_ly SF_size_lx //=.
revert ptd' ; apply SF_cons_ind with (s := ptd) => /= [x0 | h ptd' IH].
easy.
rewrite Riemann_sum_cons.
rewrite (SF_rev_cons (-fst h, -snd h) (mkSF_seq (- SF_h ptd') (seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd')))).
rewrite -IH => {IH}.
set s := {| SF_h := - SF_h ptd'; SF_t := seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd') |}.
rewrite Riemann_sum_rcons.
rewrite SF_lx_rev.
have H : (forall s x0, last x0 (rev s) = head x0 s).
move => T s0 x0.
case: s0 => [ | x1 s0] //=.
rewrite rev_cons.
by rewrite last_rcons.
rewrite H /=.
rewrite plus_comm.
apply: (f_equal (fun x => plus (scal x _) _)).
simpl ; ring.
