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
admit.
