Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import List.
Require Import Rcomplements.
Open Scope R_scope.
Section Compactness.
Fixpoint Tn n T : Type := match n with | O => unit | S n => (T * Tn n T)%type end.
Fixpoint bounded_n n : Tn n R -> Tn n R -> Tn n R -> Prop := match n return Tn n R -> Tn n R -> Tn n R -> Prop with | O => fun a b x : Tn O R => True | S n => fun a b x : Tn (S n) R => let '(a1,a2) := a in let '(b1,b2) := b in let '(x1,x2) := x in a1 <= x1 <= b1 /\ bounded_n n a2 b2 x2 end.
Fixpoint close_n n d : Tn n R -> Tn n R -> Prop := match n return Tn n R -> Tn n R -> Prop with | O => fun x t : Tn O R => True | S n => fun x t : Tn (S n) R => let '(x1,x2) := x in let '(t1,t2) := t in Rabs (x1 - t1) < d /\ close_n n d x2 t2 end.
End Compactness.

Lemma compactness_value : forall n a b (delta : Tn n R -> posreal), { d : posreal | forall x, bounded_n n a b x -> ~~ exists t, bounded_n n a b t /\ close_n n (delta t) x t /\ d <= delta t }.
Proof.
intros n a b delta.
set (P d := d <= 1 /\ forall x, bounded_n n a b x -> exists t, bounded_n n a b t /\ close_n n (delta t) x t /\ d <= delta t).
assert (P1 : exists d, P d).
exists 0.
split.
apply Rle_0_1.
intros x Hx.
exists x.
split.
exact Hx.
split.
clear.
induction n.
easy.
destruct x as (x,x').
split.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply (IHn (fun x' => delta (x,x'))).
apply Rlt_le.
apply cond_pos.
assert (P2 : bound P).
exists 1.
now intros d (Hd,_).
set (d := completeness P P2 P1).
assert (P3 : 0 < proj1_sig d).
revert d.
case completeness.
intros d (Hd1,Hd2).
simpl.
apply Rnot_le_lt.
intros Hd3.
apply (compactness_list n a b delta).
intros (l,Hl).
set (v := fold_right (fun t acc => mkposreal _ (Rmin_stable_in_posreal (delta t) acc)) (mkposreal _ Rlt_0_1) l).
apply (Rlt_not_le _ _ (cond_pos v)).
apply Rle_trans with (2 := Hd3).
apply Hd1.
split.
unfold v.
clear.
induction l.
apply Rle_refl.
simpl.
apply Rle_trans with (2 := IHl).
apply Rmin_r.
intros x Hx.
destruct (Hl x Hx) as (t,(Ht1,Ht2)).
exists t.
split.
apply Ht2.
split.
apply Ht2.
clear -Ht1.
induction l.
easy.
simpl in Ht1.
destruct Ht1 as [Ht1|Ht1].
simpl.
rewrite Ht1.
apply Rmin_l.
simpl.
eapply Rle_trans with (1 := Rmin_r _ _).
now apply IHl.
exists (mkposreal _ (Fourier_util.Rlt_mult_inv_pos _ _ P3 Rlt_R0_R2)).
intros x Hx.
simpl.
refine (_ (completeness_any P _ P1 P2 (proj1_sig d / 2) _)).
intros HP.
contradict HP.
contradict HP.
destruct HP as (_,HP).
now apply HP.
intros u v Huv (Pv1,Pv2).
split.
now apply Rle_trans with v.
intros z Hz.
destruct (Pv2 z Hz) as (t,Ht).
exists t.
split.
apply Ht.
split.
apply Ht.
apply Rle_trans with (1 := Huv).
apply Ht.
fold d.
rewrite -(Rplus_0_r (proj1_sig d / 2)).
rewrite {2}(double_var (proj1_sig d)).
apply Rplus_lt_compat_l.
apply Fourier_util.Rlt_mult_inv_pos.
exact P3.
apply Rlt_R0_R2.
