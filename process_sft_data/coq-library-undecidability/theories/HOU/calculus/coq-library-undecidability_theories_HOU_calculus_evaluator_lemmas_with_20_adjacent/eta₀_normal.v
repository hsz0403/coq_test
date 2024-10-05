Set Implicit Arguments.
Require Import Morphisms Setoid.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics confluence typing order normalisation.
Set Default Proof Using "Type".
Section Evaluator.
Context {X: Const}.
Definition xi := evaluator.E (@rho X) _.
Definition eta (s: exp X) {Gamma A} (H: Gamma ⊢ s : A) := proj1_sig (compute_evaluation_step (termination_steps H)).
Definition eta₀ (s: exp X) {Gamma n A} (H: Gamma ⊢(n) s : A) := proj1_sig (compute_evaluation_step (ordertyping_termination_steps H)).
Arguments eta _ {_} {_} _.
Arguments eta₀ _ {_} {_} {_} _.
Section Correctness.
Variable (Gamma: ctx) (n: nat) (s: exp X) (A: type) (H: Gamma ⊢ s : A) (H₀: Gamma ⊢(n) s : A).
End Correctness.
End Evaluator.
Arguments eta {_} _ {_} {_} _.
Arguments eta₀ {_} _ {_} {_} {_} _.

Lemma xi_correct s t: s ▷ t <-> exists n, xi n s = Some t.
Proof.
split; intros ?; eapply E_correct_tak; try eapply tak_fun_rho.
all: eauto using sandwich_step, sandwich_steps.
Admitted.

Lemma xi_monotone n m s t: n <= m -> xi n s = Some t -> xi m s = Some t.
Proof.
Admitted.

Lemma compute_evaluation_step (s: exp X): (exists t, s ▷ t) -> { t | s ▷ t }.
Proof.
intros; eapply compute_evaluation with (S := par) (rho := rho); eauto using tak_fun_rho.
Admitted.

Lemma eta_correct: s ▷ eta s H.
Proof.
unfold eta.
Admitted.

Lemma eta₀_correct: s ▷ eta₀ s H₀.
Proof.
unfold eta₀.
Admitted.

Lemma eta_normal: normal (eta s H).
Proof.
Admitted.

Lemma eta_typing: Gamma ⊢ eta s H : A.
Proof.
eapply preservation_under_steps.
rewrite <-eta_correct.
Admitted.

Lemma eta₀_typing: Gamma ⊢(n) eta₀ s H₀ : A.
Proof.
eapply ordertyping_preservation_under_steps.
rewrite <-eta₀_correct.
Admitted.

Lemma eta₀_normal: normal (eta₀ s H₀).
Proof.
destruct eta₀_correct; eauto.
