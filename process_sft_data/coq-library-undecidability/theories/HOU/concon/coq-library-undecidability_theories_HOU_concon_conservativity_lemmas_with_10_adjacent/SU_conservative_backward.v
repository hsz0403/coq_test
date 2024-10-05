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
Admitted.

Lemma linearize_consts (S: list (exp X)): consts (linearize_terms S) === Consts S.
Proof.
unfold linearize_terms.
cbn; simplify.
split; unfold Consts; intros ? [x] % in_flat_map; eapply in_flat_map.
all: intuition; try mapinj.
eexists; intuition; eauto.
now rewrite consts_ren in H1.
exists (ren shift x); intuition.
Admitted.

Lemma unification_downcast_eqs sigma Delta (E: eqs X) Gamma L: (Gamma ⊢₊₊(n) E : L) -> (Delta ⊩ sigma : Gamma) -> (sigma •₊ left_side E) ≡₊ (sigma •₊ right_side E) -> exists Sigma tau, Sigma ⊩(n) tau : Gamma /\ (tau •₊ left_side E) ≡₊ (tau •₊ right_side E).
Proof using Leq.
intros T1 T2 H.
pose (P x := x ∈ Vars' E).
pose (s := linearize_terms (left_side E)).
pose (t := linearize_terms (right_side E)).
edestruct (downcast_variables) with (s := s) (t := t) as (Sigma' & tau' & T' & H' & O'); eauto.
1: unfold s, t; now rewrite !linearize_terms_subst, linearize_terms_equiv.
clear T2 H sigma Delta.
edestruct (downcast_constants) with (s := s) (t := t) as (Sigma'' & tau'' & T'' & H'' & O'' & C''); eauto; clear T' H' tau'.
edestruct (normalise_subst) as (tau''' & R & H & T); eauto.
edestruct ordertyping_weak_ordertyping with (s := s) (t := t) (sigma := tau''').
-
intros.
eapply ordertyping_from_basetyping.
+
intros ?; erewrite consts_subset_steps; eauto.
intros H2 % C''.
cbn [Consts flat_map] in H2.
simplify in H2.
unfold s, t in H2.
rewrite !linearize_consts in H2.
destruct H2; eapply typing_Consts.
eapply left_ordertyping; eauto.
eauto.
eapply right_ordertyping; eauto.
eauto.
+
eauto.
+
domin H0; eauto.
+
simplify in H1.
unfold s, t in H1; rewrite !linearize_vars in H1.
destruct H1 as [H1|H1]; eapply Vars_listordertyping in H1.
2, 4: eauto using left_ordertyping, right_ordertyping.
all: destruct H1 as [? [H1 H2]]; rewrite H0 in H1; injection H1 as ->; eauto.
+
simplify; rewrite O', O''; cbn; eauto.
-
rewrite !subst_pointwise_equiv with (sigma := tau''') (tau := tau''); eauto.
-
destruct H0 as [tau].
exists x.
exists tau.
destruct H0; split; eauto.
Admitted.

Lemma unification_monotone_forward n (I: orduni n X): OU n X I -> OU (S n) X (unification_monotone I).
Proof.
intros (Delta & sigma & T & H).
exists Delta; exists sigma.
intuition.
Admitted.

Lemma unification_monotone_backward n (I: orduni n X): 1 <= n -> OU (S n) X (unification_monotone I) -> OU n X I.
Proof.
intros Leq (Delta & sigma & T & H).
unfold OU.
eapply unification_downcast; eauto.
Admitted.

Lemma unification_conservative_forward n (I: orduni n X): OU n X I -> U X (unification_conservative I).
Proof.
intros (Delta & sigma & T & H).
exists Delta; exists sigma.
intuition.
Admitted.

Lemma unification_conservative_backward n (I: orduni n X): 1 <= n -> U X (unification_conservative I) -> OU n X I.
Proof.
intros Leq (Delta & sigma & T & H).
unfold OU.
Admitted.

Lemma SU_monotone_forward n (I: ordsysuni X n): SOU X n I -> SOU X (S n) (SU_monotone I).
Proof.
intros (Delta & sigma & T & H).
exists Delta; exists sigma.
intuition.
Admitted.

Lemma SU_monotone_backward n (I: ordsysuni X n): 1 <= n -> SOU X (S n) (SU_monotone I) -> SOU X n I.
Proof.
intros Leq (Delta & sigma & T & H).
unfold OU.
edestruct unification_downcast_eqs as (Sigma & tau & H1); eauto using equiv_pointwise_eqs, @H₀'.
intros ???; eapply ordertyping_soundness; eauto.
Admitted.

Lemma SU_conservative_forward n (I: ordsysuni X n): SOU X n I -> SU X (SU_conservative I).
Proof.
intros (Delta & sigma & T & H).
exists Delta; exists sigma.
intuition.
Admitted.

Theorem unification_step n: 1 <= n -> OU n X ⪯ OU (S n) X.
Proof.
Admitted.

Theorem unification_steps n m: 1 <= n <= m -> OU n X ⪯ OU m X.
Proof.
Admitted.

Theorem unification_conserve n: 1 <= n -> OU n X ⪯ U X.
Proof.
Admitted.

Theorem systemunification_step n: 1 <= n -> @SOU X n ⪯ @SOU X (S n).
Proof.
Admitted.

Theorem systemunification_steps n m: 1 <= n <= m -> @SOU X n ⪯ @SOU X m.
Proof.
Admitted.

Theorem systemunification_conserve n: 1 <= n -> @SOU X n ⪯ @SU X.
Proof.
Admitted.

Lemma SU_conservative_backward n (I: ordsysuni X n): 1 <= n -> SU X (SU_conservative I) -> SOU X n I.
Proof.
intros Leq (Delta & sigma & T & H).
edestruct unification_downcast_eqs as (Sigma & tau & H1); eauto using equiv_pointwise_eqs, @H₀'.
exists Sigma, tau; intuition; eauto using equiv_eqs_pointwise.
