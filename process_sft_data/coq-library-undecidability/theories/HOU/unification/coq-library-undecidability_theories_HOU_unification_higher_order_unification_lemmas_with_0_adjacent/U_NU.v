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

Lemma U_NU I: U X I <-> NU I.
Proof.
split; intros (Delta & sigma & H1 & H2); [| exists Delta; exists sigma; intuition].
eapply normalise_subst in H1 as (tau & H5 & H6 & H7).
pose (theta x := if nth (Gammaᵤ I) x then tau x else var x).
exists Delta.
exists theta.
intuition.
+
intros ???; unfold theta; rewrite H; eapply H7; eauto.
+
rewrite subst_pointwise_equiv with (sigma0 := theta) (tau0 := sigma).
rewrite subst_pointwise_equiv with (sigma0 := theta) (tau0 := sigma); eauto.
all: intros ? H; eapply typing_variables in H; eauto; domin H.
all: unfold theta; now rewrite H, H5.
+
unfold theta; destruct nth eqn: ?; [|eauto].
domin Heqo; eauto.
