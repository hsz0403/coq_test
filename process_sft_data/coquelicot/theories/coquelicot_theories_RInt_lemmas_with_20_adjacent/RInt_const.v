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

Lemma RInt_const (a b : R) (c : V) : RInt (fun _ => c) a b = scal (b - a) c.
Proof.
apply is_RInt_unique.
exact: is_RInt_const.
