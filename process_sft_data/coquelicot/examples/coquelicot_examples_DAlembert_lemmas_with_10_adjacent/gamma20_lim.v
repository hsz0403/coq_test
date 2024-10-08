Require Import Reals.
Require Import Rcomplements Derive RInt Hierarchy Derive_2d.
Require Import AutoDerive.
Require Import mathcomp.ssreflect.ssreflect.
Local Open Scope R_scope.
Ltac auto_derive_2 := match goal with | |- is_derive_n ?f 2 ?x ?d => auto_derive_fun f ; match goal with | |- (forall x, _ -> is_derive _ x (@?d x)) -> _ => let H := fresh "H" in let u := fresh "u" in intro H ; apply (is_derive_ext d) ; [ intro u ; apply sym_eq, is_derive_unique ; apply H | auto_derive ] ; clear H end end.
Section DAlembert.
Parameter c : R.
Hypothesis Zc : c <> 0.
Parameter u0 : R -> R.
Hypothesis Du0 : forall x, ex_derive (fun u => u0 u) x.
Hypothesis D2u0 : forall x, ex_derive_n (fun u => u0 u) 2 x.
Section Alpha.
Definition alpha x t := 1/2 * (u0 (x + c * t) + u0 (x - c * t)).
Definition alpha20 x t := 1/2 * (Derive_n u0 2 (x + c * t) + Derive_n u0 2 (x - c * t)).
Definition alpha02 x t := c^2/2 * (Derive_n u0 2 (x + c * t) + Derive_n u0 2 (x - c * t)).
End Alpha.
Parameter u1 : R -> R.
Hypothesis Du1 : forall x, ex_derive (fun u => u1 u) x.
Section Beta.
Definition beta (x t : R) := 1/(2*c) * RInt (fun u => u1 u) (x - c * t) (x + c * t).
Definition beta20 x t := 1/(2*c) * (Derive (fun u => u1 u) (x + c * t) - Derive (fun u => u1 u) (x - c * t)).
Definition beta01 x t := 1/2 * (u1 (x + c * t) + u1 (x - c * t)).
Definition beta02 x t := c/2 * (Derive (fun u => u1 u) (x + c * t) - Derive (fun u => u1 u) (x - c * t)).
End Beta.
Hypothesis f : R -> R -> R.
Section Gamma.
Definition gamma x t := 1/(2*c) * RInt (fun tau => RInt (fun xi => f xi tau) (x - c * (t - tau)) (x + c * (t - tau))) 0 t.
Definition gamma20 x t := 1/(2*c) * RInt (fun tau => Derive (fun u => f u tau) (x + c * (t - tau)) - Derive (fun u => f u tau) (x - c * (t - tau))) 0 t.
Definition gamma02 x t := (f x t + c/2 * RInt (fun tau => Derive (fun u => f u tau) (x + c * (t - tau)) - Derive (fun u => f u tau) (x - c * (t - tau))) 0 t).

Lemma alpha_20_lim : forall x t, is_derive_n (fun u => alpha u t) 2 x (alpha20 x t).
Proof.
intros x t.
unfold alpha.
auto_derive_2.
repeat split ; apply Du0.
repeat split ; apply D2u0.
unfold alpha20, Derive_n, Rminus.
Admitted.

Lemma alpha_02_lim : forall x t, is_derive_n (fun u => alpha x u) 2 t (alpha02 x t).
Proof.
intros x t.
unfold alpha.
auto_derive_2.
repeat split ; apply Du0.
repeat split ; apply D2u0.
unfold alpha02, Derive_n, Rminus, Rdiv.
Admitted.

Lemma Cu1 : forall x, continuity_pt (fun u => u1 u) x.
intros x.
destruct (Du1 x) as (l,Hl).
apply derivable_continuous_pt.
unfold derivable_pt, derivable_pt_abs.
exists l.
Admitted.

Lemma continuity_implies_ex_Rint: forall f a b, (forall x, continuity_pt f x) -> ex_RInt f a b.
intros f a b H.
case (Rle_or_lt a b); intros H1.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt.
exact H1.
intros x _; apply H.
apply ex_RInt_swap.
apply ex_RInt_Reals_1.
apply continuity_implies_RiemannInt.
left; exact H1.
Admitted.

Lemma Iu1: forall a b, ex_RInt (fun u => u1 u) a b.
intros a b.
apply continuity_implies_ex_Rint.
Admitted.

Lemma beta20_lim : forall x t, is_derive_n (fun u => beta u t) 2 x (beta20 x t).
Proof.
intros x t.
unfold beta.
auto_derive_2.
split.
apply Iu1.
repeat split.
apply filter_forall.
apply Cu1.
apply filter_forall.
apply Cu1.
repeat split ; apply Du1.
unfold beta20, Rminus.
Admitted.

Lemma beta01_lim : forall x t, is_derive (fun u => beta x u) t (beta01 x t).
Proof.
intros x t.
unfold beta.
auto_derive.
split.
apply Iu1.
repeat split.
apply filter_forall.
apply Cu1.
apply filter_forall.
apply Cu1.
unfold beta01, Rminus, Rdiv.
Admitted.

Lemma beta02_lim : forall x t, is_derive_n (fun u => beta x u) 2 t (beta02 x t).
Proof.
intros x t.
unfold beta.
auto_derive_2.
split.
apply Iu1.
repeat split.
apply filter_forall.
apply Cu1.
apply filter_forall.
apply Cu1.
repeat split ; apply Du1.
unfold beta02, Rminus, Rdiv.
Admitted.

Lemma gamma02_lim : forall x t, is_derive_n (fun u => gamma x u) 2 t (gamma02 x t).
Proof.
intros x t.
unfold gamma.
auto_derive_2.
repeat split.
apply locally_2d_forall => y z.
admit.
intros t' _.
admit.
apply filter_forall => y.
admit.
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
admit.
exists (mkposreal _ Rlt_0_1).
simpl.
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
admit.
exists (mkposreal _ Rlt_0_1).
simpl.
intros t' u' _ _.
repeat split.
apply continuity_implies_ex_Rint => y.
admit.
apply filter_forall => y.
admit.
apply filter_forall => y.
admit.
repeat split.
apply locally_2d_forall => y z.
admit.
apply locally_2d_forall => y z.
admit.
intros x' _.
admit.
apply filter_forall => y.
admit.
apply filter_forall => y.
admit.
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
admit.
exists (mkposreal _ Rlt_0_1).
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
admit.
exists (mkposreal _ Rlt_0_1).
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
admit.
exists (mkposreal _ Rlt_0_1).
intros t' u' _ _.
admit.
apply locally_2d_forall => y z.
admit.
intros t' _.
admit.
apply filter_forall => y.
admit.
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
admit.
exists (mkposreal _ Rlt_0_1).
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
admit.
exists (mkposreal _ Rlt_0_1).
intros t' u' _ _.
repeat split.
admit.
admit.
unfold gamma02.
ring_simplify.
rewrite Rplus_opp_r Rmult_0_r Ropp_0 Rplus_0_r.
rewrite RInt_point Rmult_0_r Rplus_0_r.
apply Rplus_eq_reg_l with (- f x t).
field_simplify.
2: exact Zc.
rewrite Rmult_1_r.
rewrite /Rdiv Rmult_comm.
rewrite Rmult_assoc (Rmult_comm _ (/2)) -Rmult_assoc.
rewrite -[Rmult]/(@scal _ R_ModuleSpace) -RInt_scal.
rewrite -RInt_scal.
apply RInt_ext => u _.
rewrite /scal /= /mult /= /Rminus.
now field.
admit.
Admitted.

Lemma gamma20_lim : forall x t, is_derive_n (fun u => gamma u t) 2 x (gamma20 x t).
Proof.
intros x t.
unfold gamma.
auto_derive_2.
repeat split.
exists (mkposreal _ Rlt_0_1).
simpl.
intros t' u' _ _.
repeat split.
apply continuity_implies_ex_Rint => y.
admit.
apply filter_forall => y.
admit.
apply filter_forall => y.
admit.
apply filter_forall => y.
apply continuity_implies_ex_Rint => z.
apply derivable_continuous_pt.
admit.
intros t' _.
admit.
repeat split.
exists (mkposreal _ Rlt_0_1).
intros t' u' _ _.
repeat split.
admit.
admit.
apply filter_forall => y.
admit.
intros t' _.
admit.
unfold gamma20.
apply f_equal.
apply RInt_ext => z _.
now rewrite 4!Rmult_1_l.
