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

Lemma lub_cara : forall E l, is_lub E l -> forall e : posreal, ~ ~ (exists x, E x /\ l - e < x).
Proof.
intros E l H e.
intro H0.
assert (forall x, ~ (E x /\ l - e < x)) as H1.
intros x Hx.
apply H0 ; now exists x.
clear H0.
unfold is_lub in H.
destruct H as (H, H0).
assert ( ~ is_upper_bound E (l-e)) as H2.
intro H2.
apply H0 in H2.
assert (0 < e) as H3.
apply (cond_pos e).
assert (l > l - e) as H4.
apply tech_Rgt_minus.
assumption.
unfold Rgt in H4.
destruct H2 as [H2 | H2].
assert (l < l) as H5.
now apply Rlt_trans with (l-e).
apply Rlt_irrefl in H5 ; contradiction.
rewrite <- H2 in H4.
apply Rlt_irrefl in H4 ; contradiction.
unfold is_upper_bound in H2.
assert (forall x : R, E x -> x <= l-e) as H3.
clear H0 ; clear H.
intro x.
assert (~ (E x /\ l - e < x)) as H.
apply H1.
clear H1.
intro H0.
assert ({l-e<x}+{l-e=x}+{l-e>x}).
apply total_order_T.
destruct H1 as [H1 | H1].
destruct H1 as [H1 | H1].
assert (E x /\ l-e < x).
now split.
contradiction.
right ; rewrite H1 ; trivial.
now left.
Admitted.

Lemma cousin : forall a b delta, ~ ~ exists ptd, pointed_subdiv ptd /\ fine delta ptd /\ SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b.
Admitted.

Lemma is_KHInt_point : forall (f : R -> V) (a : R), is_KHInt f a a zero.
Proof.
intros f a.
unfold is_KHInt.
apply filterlim_ext with (fun ptd : @SF_seq R => @zero V).
intro ptd.
rewrite Rminus_eq_0 sign_0.
rewrite scal_zero_l ; easy.
intros P HP.
unfold filtermap.
destruct HP as (eps, HPeps).
exists (fun x : R => {| pos := 1 ; cond_pos := Rlt_0_1 |}).
intros ptd Hptd Hptd2.
apply HPeps.
Admitted.

Lemma ex_KHInt_point : forall (f : R -> V) (a : R), ex_KHInt f a a.
Proof.
Admitted.

Lemma is_KHInt_const : forall (a b : R) (c : V), is_KHInt (fun x : R => c) a b (scal (b-a) c).
Proof.
intros a b c.
intros P HP.
destruct HP as (eps, HPeps).
exists (fun x : R => eps).
intros ptd Hptd Hptd2.
apply HPeps.
rewrite Riemann_sum_const.
destruct Hptd2 as (Hptd0, Hptd1).
destruct Hptd1 as (Hptd1, Hptd2).
rewrite Hptd2.
rewrite Hptd1.
rewrite scal_assoc.
replace (mult (sign (b - a)) (Rmax a b - Rmin a b)) with (b-a).
apply ball_center.
Admitted.

Lemma ex_KHInt_const : forall (a b : R) (c : V), ex_KHInt (fun x : R => c) a b.
Proof.
Admitted.

Lemma is_KHInt_unique : forall (f : R -> V) (a b : R) (l : V), is_KHInt f a b l -> KHInt f a b = l.
Proof.
intros f a b l H.
apply filterlim_locally_unique with (2 := H).
apply KHInt_correct.
Admitted.

Lemma KHInt_point : forall (f : R -> V) (a : R), KHInt f a a = zero.
Proof.
intros f a.
apply is_KHInt_unique.
Admitted.

Lemma KHInt_const : forall (a b : R) (v : V), KHInt (fun _ => v) a b = scal (b - a) v.
Proof.
intros a b v.
apply is_KHInt_unique.
Admitted.

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
Admitted.

Lemma KHInt_correct : forall (f : R -> V) (a b : R), ex_KHInt f a b -> is_KHInt f a b (KHInt f a b).
Proof.
intros f a b [v Hv].
unfold KHInt.
apply iota_correct.
exists v.
split.
exact Hv.
intros w Hw.
apply filterlim_locally_unique with (1 := Hv) (2 := Hw).
