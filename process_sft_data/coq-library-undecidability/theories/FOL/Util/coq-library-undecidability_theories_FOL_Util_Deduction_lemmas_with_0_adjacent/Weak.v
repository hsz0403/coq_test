From Undecidability Require Import FOL.Util.Tarski FOL.Util.Syntax.
Import FragmentSyntax.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Ltac comp := repeat (progress (cbn in *; autounfold in *)).
Inductive peirce := class | intu.
Existing Class peirce.
Section ND_def.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Reserved Notation "A ⊢ phi" (at level 61).
Implicit Type p : peirce.
Implicit Type ff : falsity_flag.
Inductive prv : forall (ff : falsity_flag) (p : peirce), list form -> form -> Prop := | II {ff} {p} A phi psi : phi::A ⊢ psi -> A ⊢ phi --> psi | IE {ff} {p} A phi psi : A ⊢ phi --> psi -> A ⊢ phi -> A ⊢ psi | AllI {ff} {p} A phi : map (subst_form ↑) A ⊢ phi -> A ⊢ ∀ phi | AllE {ff} {p} A t phi : A ⊢ ∀ phi -> A ⊢ phi[t..] | Exp {p} A phi : prv p A falsity -> prv p A phi | Ctx {ff} {p} A phi : phi el A -> A ⊢ phi | Pc {ff} A phi psi : prv class A (((phi --> psi) --> phi) --> phi) where "A ⊢ phi" := (prv _ A phi).
Arguments prv {_} _ _.
Context {ff : falsity_flag}.
Context {p : peirce}.
End ND_def.
Hint Constructors prv : core.
Arguments prv {_ _ _ _} _ _.
Notation "A ⊢ phi" := (prv A phi) (at level 30).
Notation "A ⊢C phi" := (@prv _ _ _ class A phi) (at level 30).
Notation "A ⊢I phi" := (@prv _ _ _ intu A phi) (at level 30).
Notation "A ⊢M phi" := (@prv _ _ falsity_off intu A phi) (at level 30).
Section Soundness.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
End Soundness.

Theorem Weak A B phi : A ⊢ phi -> A <<= B -> B ⊢ phi.
Proof.
intros H.
revert B.
induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
