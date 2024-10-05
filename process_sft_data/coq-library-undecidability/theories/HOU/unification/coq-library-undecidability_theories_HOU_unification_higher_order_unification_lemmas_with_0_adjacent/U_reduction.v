Require Import List Lia.
Import ListNotations.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics equivalence typing order evaluator.
Set Default Proof Using "Type".
Section UnificationDefinitions.
Context {X: Const}.
Class uni := { Gammaᵤ : ctx; sᵤ : exp X; tᵤ : exp X; Aᵤ : type; H1ᵤ : Gammaᵤ ⊢ sᵤ : Aᵤ; H2ᵤ : Gammaᵤ ⊢ tᵤ : Aᵤ }.
Definition U (I: uni) := exists (Delta: ctx) (sigma: fin -> exp X), Delta ⊩ sigma : Gammaᵤ /\ sigma • sᵤ ≡ sigma • tᵤ.
End UnificationDefinitions.
Arguments uni _ : clear implicits.
Arguments U _ : clear implicits.
Hint Resolve H1ᵤ H2ᵤ : core.
Definition NU {X: Const} (I: uni X) := exists Delta sigma, Delta ⊩ sigma : Gammaᵤ /\ sigma • sᵤ ≡ sigma • tᵤ /\ forall x, normal (sigma x).
Section Normalisation.
Section SubstitutionTransformations.
Variable (X: Const) (n: nat) (s t: exp X) (A: type) (Gamma: ctx).
Hypothesis (Leq: 1 <= n).
Hypothesis (T1: Gamma ⊢(n) s : A) (T2: Gamma ⊢(n) t : A).
Implicit Types (Delta: ctx) (sigma : fin -> exp X).
End SubstitutionTransformations.
Variable (X: Const).
Arguments sᵤ {_} _.
Arguments tᵤ {_} _.
Arguments Gammaᵤ {_} _.
Arguments Aᵤ {_} _.
Program Instance uni_normalise (I: uni X) : uni X := { Gammaᵤ := Gammaᵤ I; sᵤ := eta (sᵤ I) H1ᵤ; tᵤ := eta (tᵤ I) H2ᵤ; Aᵤ := Aᵤ I }.
Next Obligation.
eapply preservation_under_steps.
rewrite <-eta_correct.
all: eauto.
Next Obligation.
eapply preservation_under_steps.
rewrite <-eta_correct.
all: eauto.
End Normalisation.

Lemma U_reduction (I I': uni X): sᵤ I ≡ sᵤ I' -> tᵤ I ≡ tᵤ I' -> Gammaᵤ I = Gammaᵤ I' -> Aᵤ I = Aᵤ I' -> U X I -> U X I'.
Proof.
intros H1 H2 H3 H4; intros (Delta & sigma & T & N); exists Delta; exists sigma; split.
rewrite <-H3; eauto.
now rewrite <-H1, <-H2, N.
