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
Admitted.

Lemma eval_comp rho xi t : eval rho (subst_term xi t) = eval (xi >> eval rho) t.
Proof.
induction t; cbn.
-
reflexivity.
-
f_equal.
rewrite map_map.
Admitted.

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
Admitted.

Lemma sat_ext' {ff : falsity_flag} rho xi phi : (forall x, rho x = xi x) -> rho ⊨ phi -> xi ⊨ phi.
Proof.
intros Hext H.
rewrite sat_ext.
exact H.
intros x.
Admitted.

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
Admitted.

Lemma sat_subst {ff : falsity_flag} rho sigma phi : (forall x, eval rho (sigma x) = rho x) -> rho ⊨ phi <-> rho ⊨ (subst_form sigma phi).
Proof.
intros H.
rewrite sat_comp.
apply sat_ext.
intros x.
Admitted.

Lemma sat_single {ff : falsity_flag} (rho : nat -> D) (Phi : form) (t : term) : (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
Proof.
rewrite sat_comp.
apply sat_ext.
Admitted.

Lemma impl_sat {ff : falsity_flag} A rho phi : sat rho (A ==> phi) <-> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
Proof.
Admitted.

Lemma impl_sat' {ff : falsity_flag} A rho phi : sat rho (A ==> phi) -> ((forall psi, psi el A -> sat rho psi) -> sat rho phi).
Proof.
Admitted.

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
