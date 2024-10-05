Set Implicit Arguments.
Require Import Lia List.
From Undecidability.HOU Require Import calculus.calculus concon.conservativity_constants unification.higher_order_unification unification.systemunification unification.nth_order_unification.
Import ListNotations.
Set Default Proof Using "Type".
Hint Rewrite @consts_Lam @consts_AppL @consts_AppR : simplify.
Section InhabitingTypes.
Variable (X: Const).
Implicit Types (s t: exp X) (Gamma Delta: ctx) (sigma tau: fin -> exp X).
Definition inhab (x: fin) (A: type) := Lambda (arity A) (@var X (arity A + x)).
End InhabitingTypes.
Hint Resolve inhab_app inhab_typing inhab_typing' ord_target' : core.
Section Conservativity.
Variable (X: Const).
Section DowncastLemmas.
Implicit Types (s t: exp X) (Gamma: ctx) (A: type).
Variable (n: nat).
Hypothesis (Leq: 1 <= n).
End DowncastLemmas.
Program Instance unification_monotone {n} (D: orduni n X): orduni (S n) X := { Gamma₀ := Gamma₀; s₀ := s₀ ; t₀ := t₀; A₀ := A₀; }.
Program Instance unification_conservative {n} (D: orduni n X): uni X := { Gammaᵤ := Gamma₀; sᵤ := s₀ ; tᵤ := t₀; Aᵤ := A₀; }.
Next Obligation.
eapply ordertyping_soundness; eauto.
Next Obligation.
eapply ordertyping_soundness; eauto.
Program Instance SU_monotone {n} (I: ordsysuni X n): ordsysuni X (S n) := { Gamma₀' := @Gamma₀' _ _ I; E₀' := @E₀' _ _ I ; L₀' := @L₀' _ _ I; }.
Next Obligation.
eapply eqs_ordertyping_step, @H₀'.
Program Instance SU_conservative {n} (I: ordsysuni X n): sysuni X := { Gammaᵤ' := @Gamma₀' _ _ I; Eᵤ' := @E₀' _ _ I ; Lᵤ' := @L₀' _ _ I; }.
Next Obligation.
eapply eqs_ordertyping_soundness, H₀'.
End Conservativity.

Lemma unification_downcast sigma Gamma s t Delta A: Delta ⊩ sigma : Gamma -> Gamma ⊢(n) s : A -> Gamma ⊢(n) t : A -> sigma • s ≡ sigma • t -> exists Sigma tau, Sigma ⊩(n) tau : Gamma /\ tau • s ≡ tau • t.
Proof using Leq.
intros T T1 T2 H.
pose (P x := x ∈ vars s ++ vars t).
edestruct (downcast_variables) as (Sigma' & tau' & T' & H' & O'); eauto; clear T H sigma Delta.
edestruct (downcast_constants) as (Sigma'' & tau'' & T'' & H'' & O'' & C''); eauto; clear T' H' tau'.
edestruct (normalise_subst) as (tau''' & R & H & T); eauto.
eapply ordertyping_weak_ordertyping with (sigma := tau''').
-
intros.
eapply ordertyping_from_basetyping.
+
intros ?; erewrite consts_subset_steps; eauto.
intros H2 % C''; cbn in H2; simplify in H2.
destruct H2; eapply typing_constants; [|eauto| |eauto]; eauto.
+
eauto.
+
domin H0; eauto.
+
simplify in H1; destruct H1; eapply vars_ordertyping_nth; eauto.
+
simplify; rewrite O', O''; cbn; eauto.
-
rewrite !subst_pointwise_equiv with (sigma := tau''') (tau := tau''); eauto.
