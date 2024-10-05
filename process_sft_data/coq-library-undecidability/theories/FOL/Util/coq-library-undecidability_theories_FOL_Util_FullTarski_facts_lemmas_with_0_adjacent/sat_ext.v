Require Import Undecidability.FOL.Util.Syntax_facts.
Require Export Undecidability.FOL.Util.FullTarski.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Vector.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Local Notation vec := Vector.t.
Section fixb.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ff : falsity_flag}.
Fixpoint impl (A : list form) phi := match A with | [] => phi | psi :: A => bin Impl psi (impl A phi) end.
End fixb.
Notation "A ==> phi" := (impl A phi) (right associativity, at level 55).
Section Tarski.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Section Substs.
Variable D : Type.
Variable I : interp D.
End Substs.
End Tarski.
Section TM.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Instance TM : interp unit := {| i_func := fun _ _ => tt; i_atom := fun _ _ => True; |}.
Fact TM_sat (rho : nat -> unit) (phi : form falsity_off) : rho ⊨ phi.
Proof.
revert rho.
remember falsity_off as ff.
induction phi; cbn; trivial.
-
discriminate.
-
destruct b0; auto.
-
destruct q; firstorder.
exact tt.
End TM.

Lemma sat_ext {ff : falsity_flag} rho xi phi : (forall x, rho x = xi x) -> rho ⊨ phi <-> xi ⊨ phi.
Proof.
induction phi as [ | b P v | | ] in rho, xi |- *; cbn; intros H.
-
reflexivity.
-
erewrite map_ext; try reflexivity.
intros t.
now apply eval_ext.
-
specialize (IHphi1 rho xi).
specialize (IHphi2 rho xi).
destruct b0; intuition.
-
destruct q.
+
split; intros H' d; eapply IHphi; try apply (H' d).
1,2: intros []; cbn; intuition.
+
split; intros [d H']; exists d; eapply IHphi; try apply H'.
1,2: intros []; cbn; intuition.
