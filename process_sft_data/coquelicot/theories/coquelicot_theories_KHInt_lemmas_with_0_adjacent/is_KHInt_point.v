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
apply ball_center.
