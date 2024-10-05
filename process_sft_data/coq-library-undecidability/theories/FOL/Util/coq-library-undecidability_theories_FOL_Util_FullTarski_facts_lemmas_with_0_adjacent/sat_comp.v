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

Lemma sat_comp {ff : falsity_flag} rho xi phi : rho ⊨ (subst_form xi phi) <-> (xi >> eval rho) ⊨ phi.
Proof.
induction phi as [ | b P v | | ] in rho, xi |- *; cbn.
-
reflexivity.
-
erewrite map_map, map_ext; try reflexivity.
intros t.
apply eval_comp.
-
specialize (IHphi1 rho xi).
specialize (IHphi2 rho xi).
destruct b0; intuition.
-
destruct q.
+
setoid_rewrite IHphi.
split; intros H d; eapply sat_ext.
2, 4: apply (H d).
all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
+
setoid_rewrite IHphi.
split; intros [d H]; exists d; eapply sat_ext.
2, 4: apply H.
all: intros []; cbn; trivial; now setoid_rewrite eval_comp.
