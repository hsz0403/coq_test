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

Lemma PCP_MU S: PCP S -> OU 3 X (PCP_to_U S).
Proof.
intros (I & ? & ? & ?).
pose (sigma := finst I (length S) .: ginst I .: var).
exists [alpha].
exists sigma.
split.
-
intros x A.
destruct x as [| [| x]]; try discriminate; cbn.
3: intros [] % nth_error_In.
all: injection 1 as ?; subst.
eapply finst_typing; (eauto 2).
eapply ginst_typing.
-
cbn -[ginst].
do 3 eapply equiv_lam_proper.
eapply equiv_app_proper.
eapply equiv_app_proper.
reflexivity.
all: unfold shift, var_zero.
all: rewrite !AppR_subst; rewrite ?Enc_subst_id; (eauto 2).
2: rewrite map_id_list.
3: intros ? ? % repeated_in; subst; reflexivity.
all: cbn; rewrite !ren_plus_base, !ren_plus_combine; change (1 + 1 + 1) with 3.
2: rewrite !AppL_ren; simplify; cbn [ren]; unfold upRen_exp_exp.
2: unfold up_ren, funcomp; cbn [scons].
replace (|S|) with (|heads S|) at 1 by now simplify.
replace (|S|) with (|tails S|) at 1 by now simplify.
rewrite !finst_equivalence, H1; simplify; (eauto 2).
rewrite ginst_equivalence; (eauto 2).
unfold ginst; asimpl.
now simplify.
