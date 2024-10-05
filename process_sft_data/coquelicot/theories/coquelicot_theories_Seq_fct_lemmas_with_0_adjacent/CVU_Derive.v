Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect Rbar.
Require Import Rcomplements.
Require Import Lim_seq Continuity Derive Series.
Require Import Lub Hierarchy.
Open Scope R_scope.
Definition CVS_dom (fn : nat -> R -> R) (D : R -> Prop) := forall x : R, D x -> ex_finite_lim_seq (fun n => fn n x).
Definition CVU_dom (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, eventually (fun n => forall x : R, D x -> Rabs ((fn n x) - real (Lim_seq (fun n => fn n x))) < eps).
Definition CVU_cauchy (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, exists N : nat, forall (n m : nat) (x : R), D x -> (N <= n)%nat -> (N <= m)%nat -> Rabs (fn n x - fn m x) < eps.
Definition is_connected (D : R -> Prop) := forall a b x, D a -> D b -> a <= x <= b -> D x.

Lemma CVU_Derive (fn : nat -> R -> R) (D : R -> Prop) : open D -> is_connected D -> CVU_dom fn D -> (forall n x, D x -> ex_derive (fn n) x) -> (forall n x, D x -> continuity_pt (Derive (fn n)) x) -> CVU_dom (fun n x => Derive (fn n) x) D -> (forall x , D x -> (is_derive (fun y => real (Lim_seq (fun n => fn n y))) x (real (Lim_seq (fun n => Derive (fn n) x))))).
Proof.
move => Ho Hc Hfn Edn Cdn Hdn.
set rn := fun x n h => match (Req_EM_T h 0) with | left _ => Derive (fn n) x | right _ => (fn n (x+h) - fn n x)/h end.
assert (Ho' : forall x : R, open (fun h : R => D (x + h))).
intros x.
apply open_comp with (2 := Ho).
intros t _.
eapply (filterlim_comp_2 (F := locally t)).
apply filterlim_const.
apply filterlim_id.
apply: filterlim_plus.
have Crn : forall x, D x -> forall n h, D (x+h) -> is_lim (rn x n) h (rn x n h).
move => x Hx n h Hh.
rewrite {2}/rn ; case: (Req_EM_T h 0) => [-> | Hh0].
apply is_lim_spec.
move => eps.
cut (locally 0 (fun y : R => y <> 0 -> Rabs ((fn n (x + y) - fn n x) / y - Derive (fn n) x) < eps)).
case => d H.
exists d => y Hy Hxy.
rewrite /rn ; case: Req_EM_T => // _ ; by apply H.
move: (Edn n x Hx) => {Edn} Edn.
apply Derive_correct in Edn.
apply is_derive_Reals in Edn.
case: (Edn eps (cond_pos eps)) => {Edn} delta Edn.
exists delta => y Hy Hxy.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
rewrite -/(Rminus _ _) Rminus_0_r in Hy.
by apply Edn.
have H : continuity_pt (fun h => ((fn n (x + h) - fn n x) / h)) h.
apply derivable_continuous_pt.
apply derivable_pt_div.
apply derivable_pt_minus.
apply derivable_pt_comp.
apply (derivable_pt_plus (fun _ => x) (fun h => h) h).
exact: derivable_pt_const.
exact: derivable_pt_id.
exists (Derive (fn n) (x + h)) ; by apply is_derive_Reals, Derive_correct, Edn.
exact: derivable_pt_const.
exact: derivable_pt_id.
exact: Hh0.
apply is_lim_spec.
move => eps.
case: (H eps (cond_pos eps)) => {H} d [Hd H].
have Hd0 : 0 < Rmin d (Rabs h).
apply Rmin_case.
exact: Hd.
by apply Rabs_pos_lt.
exists (mkposreal _ Hd0) => /= y Hy Hhy.
rewrite /rn ; case: Req_EM_T => /= Hy'.
contradict Hy.
apply Rle_not_lt.
rewrite /abs /minus /plus /opp /=.
rewrite Hy' -/(Rminus _ _) Rminus_0_l Rabs_Ropp ; by apply Rmin_r.
apply (H y) ; split.
split.
exact: I.
by apply sym_not_eq.
by apply Rlt_le_trans with (1 := Hy), Rmin_l.
have Hrn : forall x, D x -> CVU_dom (rn x) (fun h : R => D (x + h)).
move => x Hx.
apply CVU_dom_cauchy => eps.
apply CVU_dom_cauchy in Hdn.
case: (Hdn eps) => {Hdn} /= N Hdn.
exists N => n m h Hh Hn Hm.
rewrite /rn ; case: Req_EM_T => Hh0.
exact: (Hdn n m x Hx Hn Hm).
replace ((fn n (x + h) - fn n x) / h - (fn m (x + h) - fn m x) / h) with (((fn n (x + h) - fn m (x + h)) - (fn n x - fn m x))/h) by (field ; auto).
case: (MVT_gen (fun x => (fn n x - fn m x)) x (x+h) (Derive (fun x => fn n x - fn m x))) => [y Hy | y Hy | z [Hz ->]].
apply Derive_correct.
apply: ex_derive_minus ; apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
apply Rmin_case ; [by apply Hx | by apply Hh].
apply Rmax_case ; [by apply Hx | by apply Hh].
split ; apply Rlt_le ; by apply Hy.
apply Rmin_case ; [by apply Hx | by apply Hh].
apply Rmax_case ; [by apply Hx | by apply Hh].
split ; apply Rlt_le ; by apply Hy.
apply derivable_continuous_pt, derivable_pt_minus.
exists (Derive (fn n) y) ; apply is_derive_Reals, Derive_correct, Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
apply Rmin_case ; [by apply Hx | by apply Hh].
apply Rmax_case ; [by apply Hx | by apply Hh].
by apply Hy.
exists (Derive (fn m) y) ; apply is_derive_Reals, Derive_correct, Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
apply Rmin_case ; [by apply Hx | by apply Hh].
apply Rmax_case ; [by apply Hx | by apply Hh].
by apply Hy.
replace (Derive (fun x1 : R => fn n x1 - fn m x1) z * (x + h - x) / h) with (Derive (fun x1 : R => fn n x1 - fn m x1) z) by (field ; auto).
rewrite Derive_minus.
apply (Hdn n m z).
apply (Hc (Rmin x (x + h)) (Rmax x (x + h))).
apply Rmin_case ; [by apply Hx | by apply Hh].
apply Rmax_case ; [by apply Hx | by apply Hh].
by apply Hz.
exact: Hn.
exact: Hm.
apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
apply Rmin_case ; [by apply Hx | by apply Hh].
apply Rmax_case ; [by apply Hx | by apply Hh].
by apply Hz.
apply Edn, (Hc (Rmin x (x + h)) (Rmax x (x + h))).
apply Rmin_case ; [by apply Hx | by apply Hh].
apply Rmax_case ; [by apply Hx | by apply Hh].
by apply Hz.
have Lrn : forall x, D x -> (forall (y : R) (n : nat), (fun h : R => D (x + h)) y -> ex_finite_lim (rn x n) y).
intros ; exists (rn x n y) ; by intuition.
move => x Hx.
case: (CVU_limits_open (rn x) _ (Ho' x) (Hrn x Hx) (Lrn x Hx) 0) => [ | H [H0 H1]].
by rewrite Rplus_0_r.
have : ex_derive (fun y : R => real (Lim_seq (fun n : nat => fn n y))) x /\ Derive (fun y : R => real (Lim_seq (fun n : nat => fn n y))) x = real (Lim_seq (fun n : nat => Derive (fn n) x)).
split.
case: H0 => df H0.
exists df.
apply is_derive_Reals => e He.
apply is_lim_spec in H0.
case: (H0 (mkposreal e He)) => {H0} /= delta H0.
destruct (Ho x Hx) as [dx Hd].
have H2 : 0 < Rmin delta dx.
apply Rmin_case ; [by apply delta | by apply dx].
exists (mkposreal _ H2) => /= h Hh0 Hh.
replace (real (Lim_seq (fun n : nat => fn n (x + h))) - real (Lim_seq (fun n : nat => fn n x))) with (real (Rbar_minus (Lim_seq (fun n : nat => fn n (x + h))) (Lim_seq (fun n : nat => fn n x)))).
rewrite -Lim_seq_minus.
replace (real (Lim_seq (fun n : nat => fn n (x + h) - fn n x)) / h) with (real (Rbar_mult (/h) (Lim_seq (fun n : nat => fn n (x + h) - fn n x)))).
rewrite -Lim_seq_scal_l.
replace (Lim_seq (fun n : nat => / h * (fn n (x + h) - fn n x))) with (Lim_seq (fun n : nat => rn x n h)).
apply H0.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
rewrite -/(Rminus _ _) Rminus_0_r ; apply Rlt_le_trans with (1 := Hh), Rmin_l.
exact: Hh0.
apply Lim_seq_ext => n.
rewrite /rn /Rdiv ; case: Req_EM_T => // _ ; exact: Rmult_comm.
case: (Lim_seq (fun n : nat => fn n (x + h) - fn n x)) => [l | | ] //=.
by field.
rewrite /Rdiv Rmult_0_l.
case: Rle_dec => // Hh1.
case: Rle_lt_or_eq_dec => //.
rewrite /Rdiv Rmult_0_l.
case: Rle_dec => // Hh1.
case: Rle_lt_or_eq_dec => //.
apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
exact: Hfn.
apply Hd.
simpl.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
ring_simplify (x + h + - x) ; apply Rlt_le_trans with (1 := Hh), Rmin_r.
apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
exact: Hfn.
apply Hd.
apply ball_center.
apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
rewrite (is_lim_seq_unique (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
easy.
apply F0.
apply ball_center.
apply F.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
ring_simplify (x + h + - x).
apply Rlt_le_trans with (1 := Hh), Rmin_r.
apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
rewrite (is_lim_seq_unique (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
by [].
apply F0.
apply ball_center.
apply F.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
ring_simplify (x + h + - x).
apply Rlt_le_trans with (1 := Hh), Rmin_r.
rewrite /Derive.
replace (Lim_seq (fun n : nat => real (Lim (fun h : R => (fn n (x + h) - fn n x) / h) 0))) with (Lim_seq (fun n : nat => real (Lim (rn x n) 0))).
rewrite H1.
case: H0 => drn H0.
rewrite (is_lim_unique _ _ _ H0).
apply f_equal, is_lim_unique.
apply is_lim_spec.
intros eps.
apply is_lim_spec in H0.
case: (H0 eps) => {H0} delta H0.
destruct (Ho x Hx) as [dx Hd].
have H2 : 0 < Rmin delta dx.
apply Rmin_case ; [by apply delta | by apply dx].
exists (mkposreal _ H2) => /= h Hh0 Hh.
replace (real (Lim_seq (fun n : nat => fn n (x + h))) - real (Lim_seq (fun n : nat => fn n x))) with (real (Rbar_minus (Lim_seq (fun n : nat => fn n (x + h))) (Lim_seq (fun n : nat => fn n x)))).
rewrite -Lim_seq_minus.
replace (real (Lim_seq (fun n : nat => fn n (x + h) - fn n x)) / h) with (real (Rbar_mult (/h) (Lim_seq (fun n : nat => fn n (x + h) - fn n x)))).
rewrite -Lim_seq_scal_l.
replace (Lim_seq (fun n : nat => / h * (fn n (x + h) - fn n x))) with (Lim_seq (fun n : nat => rn x n h)).
apply H0.
apply Rlt_le_trans with (1 := Hh0), Rmin_l.
exact: Hh.
apply Lim_seq_ext => n.
rewrite /rn /Rdiv ; case: Req_EM_T => // _ ; exact: Rmult_comm.
case: (Lim_seq (fun n : nat => fn n (x + h) - fn n x)) => [l | | ] //=.
by field.
rewrite /Rdiv Rmult_0_l.
case: Rle_dec => // Hh1.
case: Rle_lt_or_eq_dec => //.
rewrite /Rdiv Rmult_0_l.
case: Rle_dec => // Hh1.
case: Rle_lt_or_eq_dec => //.
apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
exact: Hfn.
apply Hd.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
ring_simplify (x + h + - x) ; rewrite -(Rminus_0_r h) ; apply Rlt_le_trans with (1 := Hh0), Rmin_r.
apply ex_finite_lim_seq_correct, CVU_CVS_dom with D.
exact: Hfn.
apply Hd.
apply ball_center.
apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
rewrite (is_lim_seq_unique (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
easy.
apply F0.
apply ball_center.
apply F.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
ring_simplify (x + h + - x).
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hh0.
rewrite -/(Rminus _ _) Rminus_0_r in Hh0.
apply Rlt_le_trans with (1 := Hh0), Rmin_r.
apply (CVU_CVS_dom fn D) in Hfn ; rewrite /CVS_dom in Hfn.
move: (fun H => Lim_seq_correct' _ (Hfn (x+h) (Hd _ H))) => F.
move: (fun H => Lim_seq_correct' _ (Hfn (x) (Hd _ H))) => F0.
rewrite (is_lim_seq_unique _ (real (Lim_seq (fun n : nat => fn n (x + h))))).
rewrite (is_lim_seq_unique (fun n : nat => fn n (x)) (real (Lim_seq (fun n : nat => fn n (x))))).
by [].
apply F0.
apply ball_center.
apply F.
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /=.
ring_simplify (x + h + - x).
rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hh0.
rewrite -/(Rminus _ _) Rminus_0_r in Hh0.
apply Rlt_le_trans with (1 := Hh0), Rmin_r.
apply Lim_seq_ext => n.
apply sym_eq, f_equal, is_lim_unique.
have Hx' : D (x + 0).
by rewrite Rplus_0_r.
rewrite (is_lim_unique _ _ _ (Crn x Hx n 0 Hx')).
apply is_lim_spec.
move: (Crn x Hx n 0 Hx') => H2 eps.
apply is_lim_spec in H2.
case: (H2 eps) => {H2} delta H2.
exists delta => y Hy Hy0.
move: (H2 y Hy Hy0).
rewrite {1}/rn ; by case: Req_EM_T.
case => H2 H3.
rewrite -H3.
by apply Derive_correct.
