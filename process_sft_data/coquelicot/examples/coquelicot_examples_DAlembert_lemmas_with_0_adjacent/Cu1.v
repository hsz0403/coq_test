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

Lemma Cu1 : forall x, continuity_pt (fun u => u1 u) x.
intros x.
destruct (Du1 x) as (l,Hl).
apply derivable_continuous_pt.
unfold derivable_pt, derivable_pt_abs.
exists l.
now apply is_derive_Reals.
