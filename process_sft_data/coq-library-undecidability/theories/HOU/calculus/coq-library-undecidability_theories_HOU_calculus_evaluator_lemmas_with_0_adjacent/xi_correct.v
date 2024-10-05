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
all: typeclasses eauto.
