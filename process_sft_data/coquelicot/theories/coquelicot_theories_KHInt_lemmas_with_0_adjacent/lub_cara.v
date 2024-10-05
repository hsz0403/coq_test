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
contradiction.
