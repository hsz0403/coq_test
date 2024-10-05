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

Lemma compactness_list : forall n a b (delta : Tn n R -> posreal), ~~ exists l, forall x, bounded_n n a b x -> exists t, In t l /\ bounded_n n a b t /\ close_n n (delta t) x t.
Proof.
induction n.
intros a b delta.
intros H.
apply H.
exists (tt :: nil).
intros x Hx.
exists tt.
repeat split.
now left.
simpl.
intros (a,a') (b,b') delta.
destruct (Rlt_le_dec b a) as [Hab|Hab].
intros H.
apply H.
exists nil.
intros (x,x') (Hx,_).
elim (Rlt_irrefl a).
apply Rle_lt_trans with (2 := Hab).
now apply Rle_trans with x.
set (P y := y <= b /\ ~~exists l, forall x, bounded_n (S n) (a,a') (y,b') x -> exists t, In t l /\ bounded_n (S n) (a,a') (b,b') t /\ close_n (S n) (delta t) x t).
assert (P1': P a).
split.
apply Hab.
simpl.
specialize (IHn a' b' (fun x' => delta (a,x'))).
contradict IHn.
contradict IHn.
destruct IHn as (l,Hl).
exists (fold_right (fun x' acc => (a,x')::acc) nil l).
intros (x,x') (Hx,Hx').
replace x with a by now apply Rle_antisym.
destruct (Hl x' Hx') as (t',(Ht1,Ht2)).
exists (a,t').
split.
clear -Ht1.
induction l.
easy.
simpl in Ht1 |- *.
destruct Ht1 as [Ht1|Ht1].
left.
now apply f_equal2.
right.
now apply IHl.
repeat split.
apply Rle_refl.
exact Hab.
apply Ht2.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
apply Ht2.
assert (P2: bound P).
exists b => y Hy.
apply Hy.
assert (P3: forall x y, x <= y -> P y -> P x).
intros x y Hxy (Py1,Py2).
split.
now apply Rle_trans with y.
contradict Py2.
contradict Py2.
destruct Py2 as (l,Py2).
exists l => [[z z']] Hz.
apply Py2.
split.
split.
apply Hz.
now apply Rle_trans with (1 := proj2 (proj1 Hz)).
apply Hz.
assert (P1: exists x, P x).
now exists a.
set (y := proj1_sig (completeness _ P2 P1)).
assert (P4: ~~exists d : posreal, P (Rmin b (y + d))).
specialize (IHn a' b' (fun x' => delta (y,x'))).
contradict IHn.
contradict IHn.
destruct IHn as (l, Hl).
set (d := fold_right (fun t acc => mkposreal _ (Rmin_stable_in_posreal (delta (y,t)) acc)) (mkposreal _ Rlt_0_1) l).
assert (Hd: 0 < d/2).
apply Fourier_util.Rlt_mult_inv_pos.
apply cond_pos.
apply Rlt_R0_R2.
exists (mkposreal _ Hd).
split.
apply Rmin_l.
refine (_ (completeness_any _ P3 P1 P2 (y - d) _)).
intros Hy.
apply: false_not_not Hy => Hy.
destruct Hy as (Hy1,Hy2).
apply: false_not_not Hy2 => Hy2.
apply.
destruct Hy2 as (l',Hl').
exists (app (fold_right (fun x' acc => (y,x')::acc) nil l) l').
simpl.
intros (x,x') (Hx,Hx').
destruct (Rle_or_lt x (y - d)) as [Hxy|Hxy].
destruct (Hl' (x,x') (conj (conj (proj1 Hx) Hxy) Hx')) as (t,(Ht1,Ht2)).
exists t.
split.
apply in_or_app.
now right.
exact Ht2.
destruct (Hl x' Hx') as (t',(Ht1,Ht2)).
exists (y, t').
split.
apply in_or_app.
left.
clear -Ht1.
induction l.
easy.
simpl in Ht1 |- *.
destruct Ht1 as [Ht1|Ht1].
left.
now apply f_equal2.
right.
now apply IHl.
do 2 split.
unfold y.
case completeness => /= z [Hz1 Hz2].
split.
now apply Hz1.
apply Hz2.
intros w Hw.
apply Hw.
apply Ht2.
apply Rlt_le_trans with d.
apply Rabs_def1.
apply Rplus_lt_reg_r with y.
ring_simplify.
apply Rle_lt_trans with (y + d/2).
now apply Rle_trans with (2 := Rmin_r b _).
apply Rplus_lt_compat_l.
rewrite -(Rplus_0_r (d/2)).
rewrite {2}(double_var d).
now apply Rplus_lt_compat_l.
apply Rplus_lt_reg_l with y.
now ring_simplify (y + (x - y)).
clearbody y.
clear -Ht1.
induction l.
easy.
simpl in Ht1.
destruct Ht1 as [Ht1|Ht1].
rewrite -Ht1.
apply: Rmin_l.
unfold d.
simpl.
apply Rle_trans with (1 := Rmin_r _ _).
now apply IHl.
apply Ht2.
fold y.
rewrite -{2}(Rplus_0_r y) -Ropp_0.
apply Rplus_lt_compat_l.
apply Ropp_lt_contravar.
apply cond_pos.
apply: false_not_not P4 => P4.
destruct P4 as (d,P4).
destruct (Rle_or_lt b y) as [Hby|Hby].
rewrite Rmin_left in P4.
apply P4.
rewrite -(Rplus_0_r b).
apply Rplus_le_compat with (1 := Hby).
apply Rlt_le.
apply cond_pos.
elimtype False.
unfold y in *.
clear y.
revert P4 Hby.
case completeness => /= y [Hy1 Hy2] P4 Hby.
apply Rle_not_lt with (1 := Hy1 (Rmin b (y + d)) P4).
apply Rmin_case.
exact Hby.
rewrite -{1}(Rplus_0_r y).
apply Rplus_lt_compat_l.
apply cond_pos.
