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

Lemma filterlim_RInt {U} {V : CompleteNormedModule R_AbsRing} : forall (f : U -> R -> V) (a b : R) F (FF : ProperFilter F) g h, (forall x, is_RInt (f x) a b (h x)) -> (filterlim f F (locally g)) -> exists If, filterlim h F (locally If) /\ is_RInt g a b If.
Proof.
intros f a b F FF g h Hfh Hfg.
wlog: a b h Hfh / (a <= b) => [Hw | Hab].
case: (Rle_lt_dec a b) => Hab.
by apply Hw.
destruct (Hw b a (fun x => opp (h x))) as [If [Hfh' Hfg']].
intro x.
by apply @is_RInt_swap.
by apply Rlt_le.
exists (opp If) ; split.
apply filterlim_ext with (fun x => opp (opp (h x))).
move => x.
by apply opp_opp.
eapply (filterlim_comp _ _ _ (fun x => opp (h x)) opp).
by apply Hfh'.
now generalize (filterlim_opp If).
by apply @is_RInt_swap.
case: Hab => Hab.
destruct (fun FF2 HF2 => filterlim_switch_dom F FF (locally_dist (fun ptd : SF_seq.SF_seq => SF_seq.seq_step (SF_seq.SF_lx ptd))) FF2 (fun ptd : SF_seq.SF_seq => SF_seq.pointed_subdiv ptd /\ SF_seq.SF_h ptd = Rmin a b /\ seq.last (SF_seq.SF_h ptd) (SF_seq.SF_lx ptd) = Rmax a b) HF2 (fun (x : U) ptd => scal (sign (b - a)) (Riemann_sum (f x) ptd)) (fun ptd => scal (sign (b - a)) (Riemann_sum g ptd)) h) as [If [Hh Hg]].
by apply locally_dist_filter.
intros P [eP HP].
assert (Hn : 0 <= ((b - a) / eP)).
apply Rdiv_le_0_compat.
apply -> Rminus_le_0.
apply Rlt_le, Hab.
apply cond_pos.
set n := (nfloor _ Hn).
exists (SF_seq.SF_seq_f2 (fun x y => x) (SF_seq.unif_part (Rmin a b) (Rmax a b) n)).
destruct (Riemann_fine_unif_part (fun x y => x) a b n).
intros u v Huv.
split.
apply Rle_refl.
exact Huv.
now apply Rlt_le, Hab.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
split.
apply H0.
apply HP.
apply Rle_lt_trans with (1 := H).
apply Rlt_div_l.
apply INRp1_pos.
unfold n, nfloor.
destruct nfloor_ex as [n' Hn'].
simpl.
rewrite Rmult_comm.
apply Rlt_div_l.
apply cond_pos.
apply Hn'.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
2: by apply Hfh.
set (M := @norm_factor _ V).
intros P [eps HP].
have He: 0 < (eps / (b - a)) / (2 * M).
apply Rdiv_lt_0_compat.
apply Rdiv_lt_0_compat.
by apply eps.
by rewrite -Rminus_lt_0.
apply Rmult_lt_0_compat.
by apply Rlt_0_2.
apply norm_factor_gt_0.
generalize (Hfg _ (locally_ball g (mkposreal _ He))) => {Hfg Hfh}.
unfold filtermap ; apply filter_imp => x Hx.
apply HP.
case => t [Ht [Ha Hb]] /=.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite 2!scal_one.
apply: norm_compat1.
generalize (Riemann_sum_minus (f x) g t) => <-.
refine (_ (Riemann_sum_norm (fun x0 : R => minus (f x x0) (g x0)) (fun _ => M * ((eps / (b - a)) / (2 * M))) t Ht _)).
move => H ; apply Rle_lt_trans with (1 := H).
rewrite Riemann_sum_const.
rewrite Hb Ha.
rewrite /scal /= /mult /=.
replace ((b - a) * (M * ((eps / (b - a)) / (2 * M)))) with (eps / 2).
rewrite {2}(double_var eps) -{1}(Rplus_0_l (eps / 2)).
apply Rplus_lt_compat_r.
apply Rdiv_lt_0_compat.
by apply eps.
by apply Rlt_0_2.
field.
split.
apply Rgt_not_eq.
apply Rlt_gt.
by rewrite -Rminus_lt_0.
apply Rgt_not_eq.
apply norm_factor_gt_0.
intros t0 Ht0.
apply Rlt_le.
apply (norm_compat2 _ _ (mkposreal _ He) (Hx t0)).
exists If ; split.
by apply Hh.
by apply Hg.
exists zero.
rewrite -Hab in Hfh |- * => {b Hab}.
split.
apply filterlim_ext with (fun _ => zero).
intros x.
apply filterlim_locally_unique with (2 := Hfh x).
apply is_RInt_point.
apply filterlim_const.
Admitted.

Lemma ex_RInt_scal : forall (f : R -> V) (a b : R) (k : R), ex_RInt f a b -> ex_RInt (fun y => scal k (f y)) a b.
Proof.
intros f a b k [If Hf].
exists (scal k If).
now apply is_RInt_scal.
