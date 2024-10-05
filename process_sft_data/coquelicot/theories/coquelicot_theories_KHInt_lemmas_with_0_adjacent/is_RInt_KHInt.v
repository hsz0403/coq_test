Require Import Reals mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.seq.
Require Import Rcomplements Hierarchy SF_seq RInt.
Definition ith_step (ptd : @SF_seq R) i := nth 0 (SF_lx ptd) (S i) - nth 0 (SF_lx ptd) i.
Definition fine (delta : R -> posreal) ptd := forall i : nat, (i < SF_size ptd)%nat -> ith_step ptd i < delta (nth 0 (SF_ly ptd) i).
Definition KH_filter (P : SF_seq -> Prop) := exists delta, forall ptd, fine delta ptd -> P ptd.
Global Instance KH_filter_filter : Filter KH_filter.
Proof.
split.
exists (fun x => {| pos := 1; cond_pos := Rlt_0_1 |}).
intros ptd H.
easy.
intros P Q HP HQ.
destruct HP as (deltaP, HP).
destruct HQ as (deltaQ, HQ).
exists (fun x => {| pos := Rmin (deltaP x) (deltaQ x) ; cond_pos := (Rmin_stable_in_posreal (deltaP x) (deltaQ x))|}).
intros ptd Hptd.
split.
apply HP.
intros i Hi.
eapply Rlt_le_trans.
now apply (Hptd i).
apply Rmin_l.
apply HQ.
intros i Hi.
eapply Rlt_le_trans.
now apply (Hptd i).
apply Rmin_r.
intros P Q HPQ HP.
destruct HP as (delta, HP).
exists delta.
intros ptd Hptd.
apply HPQ ; now apply HP.
Definition KH_fine (a b : R) := within (fun ptd => pointed_subdiv ptd /\ SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b) KH_filter.
Section is_KHInt.
Context {V : NormedModule R_AbsRing}.
Definition is_KHInt (f : R -> V) (a b : R) (If : V) := filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd)) (KH_fine a b) (locally If).
Definition ex_KHInt f a b := exists If : V, is_KHInt f a b If.
End is_KHInt.
Section KHInt.
Context {V : CompleteNormedModule R_AbsRing}.
Definition KHInt (f : R -> V) (a b : R) := iota (is_KHInt f a b).
End KHInt.

Lemma is_RInt_KHInt : forall (f : R -> V) (a b : R) (l : V), is_RInt f a b l -> is_KHInt f a b l.
Proof.
intros f a b I.
unfold is_RInt, is_KHInt.
apply filterlim_filter_le_1.
unfold filter_le, Riemann_fine, KH_fine, within, KH_filter, locally_dist.
intros P [delta HPdelta].
exists (fun _ => delta).
intros ptd Hptd1 Hptd2.
apply HPdelta.
2: exact Hptd2.
clear -Hptd1 Hptd2.
unfold fine in Hptd1.
revert Hptd1 Hptd2.
assert ((forall i : nat, (i < SF_size ptd)%nat -> ith_step ptd i < delta) -> pointed_subdiv ptd /\ SF_h ptd >= Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b -> seq_step (SF_lx ptd) < delta) as H0.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | h ptd IH] H.
intros H0.
apply cond_pos.
intro H0.
rewrite SF_lx_cons.
unfold seq_step ; simpl.
apply Rmax_case.
specialize (H 0%nat).
unfold ith_step in H.
rewrite SF_lx_cons in H.
simpl in H.
rewrite Rabs_right.
apply H.
rewrite SF_size_cons.
apply lt_0_Sn.
destruct H0 as (H0, H1).
unfold pointed_subdiv in H0.
apply Rge_minus.
apply Rle_ge.
specialize (H0 0%nat).
apply Rle_trans with (nth 0 (SF_ly (SF_cons h ptd)) 0) ; apply H0 ; rewrite SF_size_cons ; apply lt_0_Sn.
apply IH.
intros i Hi.
specialize (H (S i)).
unfold ith_step.
unfold ith_step in H.
change (nth 0 (SF_lx ptd) (S i)) with (nth 0 (SF_lx (SF_cons h ptd)) (S (S i))).
change (nth 0 (SF_lx ptd) i) with (nth 0 (SF_lx (SF_cons h ptd)) (S i)).
apply H.
rewrite SF_size_cons ; now apply lt_n_S.
split.
apply ptd_cons with h.
apply H0.
split.
apply Rge_trans with (SF_h (SF_cons h ptd)).
2:apply H0.
2:apply H0.
apply Rle_ge.
destruct H0 as (H0, H1).
unfold pointed_subdiv in H0.
specialize (H0 0%nat).
change (SF_h (SF_cons h ptd)) with (nth 0 (SF_lx (SF_cons h ptd)) 0).
change (SF_h ptd) with (nth 0 (SF_lx (SF_cons h ptd)) 1).
apply Rle_trans with (nth 0 (SF_ly (SF_cons h ptd)) 0) ; apply H0 ; rewrite SF_size_cons ; apply lt_0_Sn.
intros H1 H2.
apply H0.
apply H1.
split.
apply H2.
split.
destruct H2 as (H2, (H3, H4)).
rewrite H3.
apply Rge_refl.
apply H2.
