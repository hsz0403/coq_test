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

Lemma is_RInt_SF (f : R -> V) (s : SF_seq) : SF_sorted Rle s -> let a := SF_h s in let b := last (SF_h s) (unzip1 (SF_t s)) in is_RInt (SF_fun (SF_map f s) zero) a b (Riemann_sum f s).
Proof.
apply SF_cons_ind with (s := s) => {s} [ x0 | x0 s IH] Hsort a b.
rewrite Riemann_sum_zero //.
by apply is_RInt_point.
-
rewrite Riemann_sum_cons.
apply is_RInt_Chasles with (SF_h s).
move: (proj1 Hsort) ; unfold a ; clear IH Hsort a b ; simpl => Hab.
eapply is_RInt_ext, is_RInt_const.
rewrite /Rmin /Rmax ; case: Rle_dec => // _ x Hx.
unfold SF_fun ; simpl.
case: Rlt_dec => //= H.
contradict H ; apply Rle_not_lt, Rlt_le, Hx.
move: Hab Hx ; apply SF_cons_dec with (s := s) => {s} /= [x1 | x1 s] Hab Hx.
case: Rle_dec (Rlt_le _ _ (proj2 Hx)) => //.
case: Rlt_dec (proj2 Hx) => //.
-
eapply is_RInt_ext, IH.
clear a IH.
revert b ; simpl.
rewrite /Rmin /Rmax ; case: Rle_dec => // Hab x Hx.
rewrite /SF_fun /=.
case: Rlt_dec => /= Hx0.
contradict Hx0.
apply Rle_not_lt.
eapply Rle_trans, Rlt_le, Hx.
by apply Hsort.
move: Hab Hx Hsort ; apply SF_cons_dec with (s := s) => {s} [x1 | x1 s] //= Hab Hx Hsort.
case: Hx => H H'.
contradict H' ; by apply Rle_not_lt, Rlt_le.
case: Rlt_dec => //= H.
contradict H ; by apply Rle_not_lt, Rlt_le, Hx.
contradict Hab.
apply (sorted_last ((SF_h s) :: (unzip1 (SF_t s))) O (proj2 Hsort) (lt_O_Sn _) (SF_h s)).
Admitted.

Lemma ex_RInt_SF (f : R -> V) (s : SF_seq) : SF_sorted Rle s -> let a := SF_h s in let b := last (SF_h s) (unzip1 (SF_t s)) in ex_RInt (SF_fun (SF_map f s) zero) a b.
Proof.
intros.
eexists.
Admitted.

Lemma ex_RInt_continuous {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b : R) : (forall z, Rmin a b <= z <= Rmax a b -> continuous f z) -> ex_RInt f a b.
Proof.
wlog: f / (forall z : R, continuous f z) => [ Hw Cf | Cf _ ].
destruct (C0_extension_le f (Rmin a b) (Rmax a b)) as [g [Cg Hg]].
by apply Cf.
apply ex_RInt_ext with g.
intros x Hx ; apply Hg ; split ; apply Rlt_le ; apply Hx.
apply Hw => // z _ ; by apply Cg.
wlog: a b / (a < b) => [Hw | Hab].
case: (Rle_lt_dec a b) => Hab.
case: Hab => Hab.
by apply Hw.
rewrite Hab ; by apply ex_RInt_point.
apply ex_RInt_swap.
by apply Hw.
assert (H := unifcont_normed_1d f a b (fun x Hx => Cf x)).
set n := fun eps => proj1_sig (seq_step_unif_part_ex a b (proj1_sig (H eps))).
set s := fun eps => (SF_seq_f2 (fun x y => ((x+y)/2)%R) (unif_part a b (n eps))).
set (f_eps := fun eps => fun x => match (Rle_dec a x) with | left _ => match (Rle_dec x b) with | left _ => SF_fun (SF_map f (s eps)) zero x | right _ => f x end | right _ => f x end).
set F := fun (P : posreal -> Prop) => exists eps : posreal, forall x : posreal, x < eps -> P x.
set If_eps := fun eps => Riemann_sum f (s eps).
assert (FF : ProperFilter F).
-
assert (forall P, F P <-> at_right 0 (fun x => 0 < x /\ forall Hx, P (mkposreal x Hx))).
split ; intros [e He].
exists e => y Hy H0 ; split => //.
move => {H0} H0.
apply He.
eapply Rle_lt_trans, Hy.
rewrite minus_zero_r.
by apply Req_le, sym_eq, Rabs_pos_eq, Rlt_le.
exists e ; intros [ y H0] Hy.
apply He.
apply Rabs_lt_between.
rewrite minus_zero_r ; split.
eapply Rlt_trans, H0.
rewrite -Ropp_0 ; apply Ropp_lt_contravar, e.
by apply Hy.
by apply H0.
case: (at_right_proper_filter 0) => H1 H2.
split.
+
intros P HP.
apply H0 in HP.
destruct (H1 _ HP) as [x [Hx Px]].
by exists (mkposreal x Hx).
destruct H2 ; split.
+
by exists (mkposreal _ Rlt_0_1).
+
intros.
apply H0.
eapply filter_imp.
2: apply filter_and ; apply H0.
2: apply H2.
2: apply H3.
intuition ; apply H4.
+
intros.
apply H0.
eapply filter_imp.
2: apply H0 ; apply H3.
intuition.
by apply H4.
by apply H2, H4.
assert (Ha : forall eps, a = (SF_h (s eps))).
intros eps ; simpl.
rewrite /Rdiv ; ring.
assert (Hb : forall eps, b = (last (SF_h (s eps)) (unzip1 (SF_t (s eps))))).
intros eps.
rewrite -(last_unif_part 0 a b (n eps)) ; simpl.
apply f_equal.
elim: {2 4}(n eps) (a + 1 * (b - a) / (INR (n eps) + 1))%R (2%nat) => [ | m IH] //= x0 k.
by rewrite -IH.
destruct (filterlim_RInt f_eps a b F FF f If_eps) as [If HI].
-
intros eps.
rewrite (Ha eps) (Hb eps).
eapply is_RInt_ext.
2: apply (is_RInt_SF f (s eps)).
rewrite -Hb -Ha.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x [Hax Hxb].
rewrite /f_eps.
case: Rle_dec (Rlt_le _ _ Hax) => // _ _.
case: Rle_dec (Rlt_le _ _ Hxb) => // _ _.
rewrite /s /SF_sorted SF_lx_f2.
by apply unif_part_sort, Rlt_le.
by apply lt_O_Sn.
-
apply (filterlim_locally f_eps) => /= eps.
rewrite /ball /= /fct_ball.
exists eps => e He t.
eapply ball_le.
apply Rlt_le, He.
apply (norm_compat1 (f t) (f_eps e t) e).
rewrite /f_eps.
case: Rle_dec => Hat.
case: Rle_dec => Hta.
rewrite SF_fun_incr.
rewrite SF_map_lx SF_lx_f2.
by apply unif_part_sort, Rlt_le.
by apply lt_O_Sn.
rewrite SF_map_lx SF_lx_f2.
rewrite last_unif_part head_unif_part.
by split.
by apply lt_O_Sn.
intros Hsort Ht.
case: sorted_dec.
+
rewrite SF_map_lx SF_lx_f2.
intros Hi ; set i := proj1_sig Hi.
rewrite SF_map_ly (nth_map 0).
apply (proj2_sig (H e)).
by split.
split ; eapply Rle_trans.
2: apply ptd_f2.
rewrite SF_lx_f2 {1}(Ha e).
apply sorted_head.
apply unif_part_sort.
by apply Rlt_le.
eapply lt_trans, (proj2_sig Hi).
eapply lt_trans ; apply lt_n_Sn.
by apply lt_O_Sn.
by apply unif_part_sort, Rlt_le.
intros x y Hxy.
lra.
rewrite SF_size_f2.
move: (proj2 (proj2_sig Hi)).
unfold i.
case: (size (unif_part a b (n e))) (proj1_sig Hi) => [ | m] /= k Hk.
by apply lt_n_O in Hk.
apply lt_S_n.
eapply lt_trans, Hk.
by apply lt_n_Sn.
apply ptd_f2.
by apply unif_part_sort, Rlt_le.
intros x y Hxy.
lra.
rewrite SF_size_f2.
move: (proj2 (proj2_sig Hi)).
unfold i ; case: (size (unif_part a b (n e))) (proj1_sig Hi) => [ | m] /= k Hk.
by apply lt_n_O in Hk.
apply lt_S_n.
eapply lt_trans, Hk.
by apply lt_n_Sn.
rewrite SF_lx_f2 ; try by apply lt_O_Sn.
rewrite {2}(Hb e).
eapply Rle_trans, (sorted_last _ i).
apply Req_le.
unfold s ; simpl.
unfold i ; elim: {1 3 6}(n e) (2%nat) (a + 1 * (b - a) / (INR (n e) + 1))%R (proj1_sig Hi) (proj2 (proj2_sig Hi)) => [ | m IH] // k x0 j Hj.
simpl in Hj ; by apply lt_S_n, lt_S_n, lt_n_O in Hj.
case: j Hj => [ | j] Hj //=.
rewrite -IH //.
apply lt_S_n.
rewrite size_mkseq.
by rewrite size_mkseq in Hj.
move: (unif_part_sort a b (n e) (Rlt_le _ _ Hab)).
unfold s.
elim: (unif_part a b (n e)) => [ | h] //=.
case => [ | h0 l] IH // [Hh Hl].
move: (IH Hl) => /=.
case: l Hl {IH} => //= ; split => // ; by apply Hl.
rewrite size_mkseq in Hi, i |- *.
apply lt_S_n.
eapply lt_le_trans.
eapply lt_trans, (proj2_sig Hi).
by apply lt_n_Sn.
rewrite /s.
elim: (n e) (a) (b) => [ | m IH] // a' b'.
apply le_n_S ; rewrite unif_part_S ; by apply IH.
apply Rle_lt_trans with (norm (minus (nth 0 (unif_part a b (n e)) (S i)) (nth 0 (unif_part a b (n e)) i))).
change norm with Rabs.
apply Rabs_le_between ; rewrite Rabs_pos_eq.
change minus with Rminus ; rewrite Ropp_minus_distr'.
rewrite /i {i}.
destruct Hi as [i [[H1 H2] H3]].
simpl sval.
cut (nth 0 (unif_part a b (n e)) i <= nth 0 (SF_ly (s e)) i <= nth 0 (unif_part a b (n e)) (S i)).
lra.
rewrite SF_ly_f2 nth_behead (nth_pairmap 0).
move: {-2 4}(S i) H2 => Si /= ; clear -H1 H3 ; lra.
now apply SSR_leq, lt_le_weak.
apply -> Rminus_le_0.
apply (sorted_nth Rle (unif_part a b (n e))).
by apply unif_part_sort, Rlt_le.
move: (proj2 (proj2_sig Hi)).
unfold i ; case: (size (unif_part a b (n e))) (proj1_sig Hi) => [ | m] j /= Hm.
by apply lt_n_O in Hm.
apply lt_S_n.
eapply lt_trans, Hm.
by apply lt_n_Sn.
eapply Rle_lt_trans.
apply nth_le_seq_step.
eapply lt_trans, (proj2_sig Hi).
by apply lt_n_S.
apply (proj2_sig (seq_step_unif_part_ex a b (proj1_sig (H e)))).
rewrite SSR_leq.
rewrite SF_size_ly.
apply le_S_n ; rewrite -SF_size_lx.
rewrite SF_lx_f2.
by apply lt_le_weak, (proj2_sig Hi).
by apply lt_O_Sn.
by apply lt_O_Sn.
+
intros Hi.
move: Hsort Ht Hi.
rewrite SF_map_lx SF_size_map SF_size_lx.
rewrite SF_lx_f2.
rewrite -SF_size_ly SF_ly_f2 size_behead size_pairmap size_mkseq.
simpl (S (Peano.pred (S (S (n e)))) - 2)%nat.
simpl (S (Peano.pred (S (S (n e)))) - 1)%nat.
simpl (Peano.pred (S (S (n e))) - 1)%nat.
rewrite -minus_n_O.
intros Hsort Ht Hi.
rewrite SF_map_ly (nth_map 0).
apply (proj2_sig (H e)).
by split.
split ; eapply Rle_trans.
2: apply ptd_f2.
rewrite SF_lx_f2 {1}(Ha e).
apply sorted_head.
apply unif_part_sort.
by apply Rlt_le.
rewrite size_mkseq.
eapply lt_trans ; apply lt_n_Sn.
by apply lt_O_Sn.
by apply unif_part_sort, Rlt_le.
intros x y Hxy.
lra.
rewrite SF_size_f2.
rewrite size_mkseq.
by apply lt_n_Sn.
apply ptd_f2.
by apply unif_part_sort, Rlt_le.
intros x y Hxy.
lra.
rewrite SF_size_f2.
rewrite size_mkseq.
by apply lt_n_Sn.
rewrite SF_lx_f2 ; try by apply lt_O_Sn.
rewrite {2}(Hb e).
apply Req_le.
rewrite (last_unzip1 _ 0).
fold (SF_last 0 (s e)).
rewrite SF_last_lx SF_lx_f2.
by rewrite (last_nth 0) size_mkseq.
apply lt_O_Sn.
apply Rle_lt_trans with (norm (minus (nth 0 (unif_part a b (n e)) (S (n e))) (nth 0 (unif_part a b (n e)) (n e)))).
change norm with Rabs.
apply Rabs_le_between ; rewrite Rabs_pos_eq.
change minus with Rminus ; rewrite Ropp_minus_distr'.
cut (nth 0 (unif_part a b (n e)) (n e) <= nth 0 (SF_ly (s e)) (n e) <= nth 0 (unif_part a b (n e)) (S (n e))).
lra.
rewrite SF_ly_f2 nth_behead (nth_pairmap 0).
move: {-2 4}(S (n e)) Hi => Si /= ; clear ; lra.
rewrite size_mkseq.
apply SSR_leq, le_refl.
apply -> Rminus_le_0.
apply (sorted_nth Rle (unif_part a b (n e))).
by apply unif_part_sort, Rlt_le.
rewrite size_mkseq ; by apply lt_n_Sn.
eapply Rle_lt_trans.
apply nth_le_seq_step.
rewrite size_mkseq ; by apply lt_n_Sn.
apply (proj2_sig (seq_step_unif_part_ex a b (proj1_sig (H e)))).
rewrite SSR_leq.
rewrite SF_size_ly.
apply le_S_n ; rewrite -SF_size_lx.
rewrite SF_lx_f2.
rewrite size_mkseq ; by apply le_refl.
by apply lt_O_Sn.
by apply lt_O_Sn.
rewrite minus_eq_zero norm_zero ; by apply e.
rewrite minus_eq_zero norm_zero ; by apply e.
Admitted.

Lemma norm_RInt_le : forall (f : R -> V) (g : R -> R) (a b : R) (lf : V) (lg : R), a <= b -> (forall x, a <= x <= b -> norm (f x) <= g x) -> is_RInt f a b lf -> is_RInt g a b lg -> norm lf <= lg.
Proof.
intros f g a b lf lg Hab H Hf Hg.
change (Rbar_le (norm lf) lg).
apply (filterlim_le (F := Riemann_fine a b)) with (fun ptd : SF_seq => norm (scal (sign (b - a)) (Riemann_sum f ptd))) (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum g ptd)).
3: apply Hg.
exists (mkposreal _ Rlt_0_1) => ptd _ [Hptd [Hh Hl]].
destruct Hab as [Hab|Hab].
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite !scal_one.
apply Riemann_sum_norm.
by [].
move => t.
rewrite Hl Hh /Rmin /Rmax ; case: Rle_dec => [_|].
apply H.
move => /Rnot_le_lt Hab'.
elim (Rlt_not_le _ _ Hab).
now apply Rlt_le.
rewrite -> Rminus_diag_eq by now apply sym_eq.
rewrite sign_0.
rewrite 2!scal_zero_l.
rewrite norm_zero ; by right.
apply filterlim_comp with (locally lf).
by apply Hf.
Admitted.

Lemma norm_RInt_le_const : forall (f : R -> V) (a b : R) (lf : V) (M : R), a <= b -> (forall x, a <= x <= b -> norm (f x) <= M) -> is_RInt f a b lf -> norm lf <= (b - a) * M.
Proof.
intros f a b lf M Hab H Hf.
apply norm_RInt_le with (1 := Hab) (2 := H) (3 := Hf).
Admitted.

Lemma norm_RInt_le_const_abs : forall (f : R -> V) (a b : R) (lf : V) (M : R), (forall x, Rmin a b <= x <= Rmax a b -> norm (f x) <= M) -> is_RInt f a b lf -> norm lf <= Rabs (b - a) * M.
Proof.
intros f a b lf M H Hf.
unfold Rabs.
case Rcase_abs => Hab.
apply Rminus_lt in Hab.
rewrite Ropp_minus_distr.
apply is_RInt_swap in Hf.
rewrite <- norm_opp.
apply norm_RInt_le_const with (3 := Hf).
now apply Rlt_le.
intros x Hx.
apply H.
now rewrite -> Rmin_right, Rmax_left by now apply Rlt_le.
apply Rminus_ge in Hab.
apply Rge_le in Hab.
apply norm_RInt_le_const with (1 := Hab) (3 := Hf).
intros x Hx.
apply H.
Admitted.

Lemma is_RInt_fct_extend_fst (f : R -> U * V) (a b : R) (l : U * V) : is_RInt f a b l -> is_RInt (fun t => fst (f t)) a b (fst l).
Proof.
intros Hf P [eP HP].
destruct (Hf (fun u : U * V => P (fst u))) as [ef Hf'].
exists eP => y Hy.
apply HP.
apply Hy.
exists ef => y H1 H2.
replace (Riemann_sum (fun t : R => fst (f t)) y) with (fst (Riemann_sum f y)).
by apply Hf'.
clear.
apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
by rewrite /Riemann_sum /=.
Admitted.

Lemma is_RInt_fct_extend_snd (f : R -> U * V) (a b : R) (l : U * V) : is_RInt f a b l -> is_RInt (fun t => snd (f t)) a b (snd l).
Proof.
intros Hf P [eP HP].
destruct (Hf (fun u : U * V => P (snd u))) as [ef Hf'].
exists eP => y Hy.
apply HP.
apply Hy.
exists ef => y H1 H2.
replace (Riemann_sum (fun t : R => snd (f t)) y) with (snd (Riemann_sum f y)).
by apply Hf'.
clear.
apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
by rewrite /Riemann_sum /=.
Admitted.

Lemma is_RInt_fct_extend_pair (f : R -> U * V) (a b : R) lu lv : is_RInt (fun t => fst (f t)) a b lu -> is_RInt (fun t => snd (f t)) a b lv -> is_RInt f a b (lu,lv).
Proof.
move => H1 H2.
apply filterlim_locally => eps.
generalize (proj1 (filterlim_locally _ _) H1 eps) => {H1} ; intros [d1 H1].
generalize (proj1 (filterlim_locally _ _) H2 eps) => {H2} ; intros [d2 H2].
simpl in H1, H2.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= ptd Hstep Hptd.
rewrite (Riemann_sum_pair f ptd) ; simpl.
split.
apply H1 => //.
by apply Rlt_le_trans with (2 := Rmin_l d1 d2).
apply H2 => //.
Admitted.

Lemma ex_RInt_fct_extend_fst (f : R -> U * V) (a b : R) : ex_RInt f a b -> ex_RInt (fun t => fst (f t)) a b.
Proof.
intros [l Hl].
exists (fst l).
Admitted.

Lemma ex_RInt_fct_extend_snd (f : R -> U * V) (a b : R) : ex_RInt f a b -> ex_RInt (fun t => snd (f t)) a b.
Proof.
intros [l Hl].
exists (snd l).
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
apply: filterlim_scal_r.
