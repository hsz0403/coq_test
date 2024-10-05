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
now exists If.
