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
Admitted.

Lemma ex_RInt_fct_extend_snd (f : R -> U * V) (a b : R) : ex_RInt f a b -> ex_RInt (fun t => snd (f t)) a b.
Proof.
intros [l Hl].
exists (snd l).
by apply is_RInt_fct_extend_snd.
