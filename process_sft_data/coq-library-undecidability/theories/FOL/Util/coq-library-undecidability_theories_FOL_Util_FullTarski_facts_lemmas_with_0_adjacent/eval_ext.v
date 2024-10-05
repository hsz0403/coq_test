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

Lemma eval_ext rho xi t : (forall x, rho x = xi x) -> eval rho t = eval xi t.
Proof.
intros H.
induction t; cbn.
-
now apply H.
-
f_equal.
apply map_ext_in.
now apply IH.
