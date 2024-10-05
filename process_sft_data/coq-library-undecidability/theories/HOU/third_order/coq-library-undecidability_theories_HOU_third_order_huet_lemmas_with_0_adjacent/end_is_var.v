Set Implicit Arguments.
Require Import RelationClasses Morphisms List Arith Lia Init.Nat Setoid.
From Undecidability.HOU Require Import std.std calculus.calculus unification.unification.
From Undecidability.HOU Require Import third_order.pcp third_order.encoding.
Import ListNotations.
Set Default Proof Using "Type".
Section HuetReduction.
Variable (X: Const).
Let v n: fin := n.
Let u n: fin := (S n).
Let h: exp X := var 0.
Let f: exp X := var 3.
Let g: exp X := var 4.
Instance PCP_to_U (S: list card) : orduni 3 X.
Proof with cbn [ord' ord alpha]; simplify; cbn; (eauto 2).
refine {| Gamma₀ := [Arr (repeat (alpha → alpha) (length S)) alpha; (alpha → alpha) → alpha]; s₀ := lambda lambda lambda h (AppR f (Enc 1 2 (heads S))) (AppR f (repeat (var (u 1)) (length S))); t₀ := lambda lambda lambda h (AppR f (Enc 1 2 (tails S))) (var (u 1) (g (var (u 1)))); A₀ := (alpha → alpha) → (alpha → alpha) → (alpha → alpha → alpha) → alpha; H1₀ := HGamma₀s₀A₀ S; H2₀ := HGamma₀t₀A₀ S; |}.
Defined.
Section ForwardDirection.
Definition ginst (I: list nat) : exp X := lambda AppL (repeat (var 0) (pred (|I|))) (var 1).
End ForwardDirection.
Section BackwardDirection.
Variables (s t: exp X) (x: nat) (sigma: fin -> exp X) (S: list (exp X)).
Hypothesis (H1: forall y, isVar (sigma y) /\ sigma y <> var x).
Hypothesis (N: normal s).
Hypothesis (EQ: S .+ sigma • s ≡ (var x) t).
End BackwardDirection.
End HuetReduction.

Lemma end_is_var: (forall x, x ∈ S -> isVar x) -> exists i e, i < |S| /\ s = var i e.
Proof using x t sigma N H1 EQ.
intros H2; edestruct @end_head_var with (X:=X) as (h' & T & s' & H5 & ?); (eauto 2).
subst s.
destruct T as [| t1 [| t2 T]].
all: cbn in EQ; specialize (H1 h').
all: destruct (sigma h') eqn: H'; cbn in *; intuition.
1, 3: eapply nth_error_In in H as H7; eapply H2 in H7.
1, 2: eapply nth_error_sapp in H; rewrite ?H in EQ.
+
destruct s'; cbn in *; intuition.
Discriminate.
+
rewrite AppR_subst in EQ; cbn in EQ.
eapply equiv_app_elim in EQ as (EQ1 & EQ2); cbn; (eauto 1); simplify.
destruct s'; cbn in *; intuition.
rewrite H in EQ1.
2: rewrite H; (eauto 3).
exfalso.
symmetry in EQ1.
eapply equiv_neq_var_app; (eauto 1); simplify; (eauto 3).
+
exists h'.
exists t1.
intuition.
eauto using nth_error_Some_lt.
Unshelve.
exact 0.
