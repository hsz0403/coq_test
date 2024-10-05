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

Lemma SU_conservative_backward n (I: ordsysuni X n): 1 <= n -> SU X (SU_conservative I) -> SOU X n I.
Proof.
intros Leq (Delta & sigma & T & H).
edestruct unification_downcast_eqs as (Sigma & tau & H1); eauto using equiv_pointwise_eqs, @H₀'.
Admitted.

Theorem unification_step n: 1 <= n -> OU n X ⪯ OU (S n) X.
Proof.
Admitted.

Theorem unification_steps n m: 1 <= n <= m -> OU n X ⪯ OU m X.
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

Theorem unification_conserve n: 1 <= n -> OU n X ⪯ U X.
Proof.
intros H; exists unification_conservative; split; eauto using unification_conservative_forward, unification_conservative_backward.
