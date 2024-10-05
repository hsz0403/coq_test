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

Lemma ginst_equivalence I (S: stack): I <> nil -> I ⊆ nats (length S) -> AppR (ren (add 3) (finst I (length S))) (repeat (var (u 1)) (| S |)) ≡ var (u 1) (ren (add 3) (ginst I) (var (u 1))).
Proof.
intros H H0.
unfold finst.
rewrite !Lambda_ren, !AppL_ren.
rewrite !map_id_list.
2: intros ? ?; mapinj; cbn; eapply H0, nats_lt in H3; now rewrite it_up_ren_lt.
rewrite AppR_Lambda'; simplify; (eauto 2).
unfold ginst; cbn [ren]; erewrite stepBeta.
2: asimpl; simplify; cbn; unfold funcomp; (eauto 2).
cbn [ren].
rewrite it_up_ren_ge; simplify; (eauto 2).
asimpl.
rewrite select_variables_subst; simplify; (eauto 2).
rewrite select_repeated; (eauto 2).
unfold ginst; cbn; asimpl; simplify.
rewrite sapp_ge_in; simplify; (eauto 3).
replace (_ - _) with 3 by lia.
destruct I; intuition.
