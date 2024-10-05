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

Theorem PCP_U3: PCP ⪯ OU 3 X.
Proof.
exists PCP_to_U.
intros C; split; eauto using PCP_MU.
rewrite OU_NOU; eauto using MU_PCP.
