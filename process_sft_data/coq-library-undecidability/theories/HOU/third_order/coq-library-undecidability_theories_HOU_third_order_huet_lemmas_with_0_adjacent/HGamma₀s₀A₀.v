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

Lemma HGamma₀s₀A₀ (S: list card) : [Arr (repeat (alpha → alpha) (length S)) alpha; (alpha → alpha) → alpha] ⊢( 3) (lambda lambda lambda h (AppR f (Enc 1 2 (heads S))) (AppR f (repeat (var (u 1)) (length S)))) : ((alpha → alpha) → (alpha → alpha) → (alpha → alpha → alpha) → alpha).
Proof.
do 4 econstructor.
econstructor.
econstructor; cbn; (eauto 1); cbn; (eauto 2).
-
eapply AppR_ordertyping with (L := repeat (alpha → alpha) (length S) ); simplify.
erewrite <-map_length; eapply Enc_typing.
all: econstructor; (eauto 2).
simplify; cbn; (eauto 3).
-
eapply AppR_ordertyping.
+
eapply repeated_ordertyping; simplify; [|eauto].
intros s H'.
eapply repeated_in in H'.
subst.
econstructor; cbn.
2: eauto.
eauto.
+
econstructor; simplify; (eauto 3).
