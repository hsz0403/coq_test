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
rewrite /mult /= ; ring.
