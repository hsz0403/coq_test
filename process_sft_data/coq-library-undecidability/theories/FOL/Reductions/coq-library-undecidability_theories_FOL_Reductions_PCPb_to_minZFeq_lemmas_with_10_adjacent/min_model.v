From Undecidability.FOL Require Import Util.FullTarski_facts Util.Syntax_facts Util.FullDeduction_facts.
From Undecidability.FOL Require Import ZF Reductions.PCPb_to_ZF Reductions.PCPb_to_minZF minZF Reductions.PCPb_to_ZFeq.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Require Import Equations.Equations.
Require Import Morphisms.
Local Notation vec := Vector.t.
Section Model.
Open Scope sem.
Context {V : Type} {I : interp V}.
Hypothesis M_ZF : forall rho, rho ⊫ ZFeq'.
Instance min_model : interp sig_empty _ V.
Proof.
split.
-
intros [].
-
now apply i_atom.
Defined.
Instance set_equiv_equiv' : Equivalence set_equiv.
Proof.
now apply set_equiv_equiv.
Instance set_equiv_elem' : Proper (set_equiv ==> set_equiv ==> iff) set_elem.
Proof.
now apply set_equiv_elem.
Instance set_equiv_sub' : Proper (set_equiv ==> set_equiv ==> iff) set_sub.
Proof.
now apply set_equiv_sub.
Instance equiv_union' : Proper (set_equiv ==> set_equiv) union.
Proof.
now apply equiv_union.
Instance equiv_power' : Proper (set_equiv ==> set_equiv) power.
Proof.
now apply equiv_power.
End Model.

Lemma min_embed_eval (rho : nat -> V) (t : term') : eval rho (embed_t t) = eval rho t.
Proof.
destruct t as [|[]].
Admitted.

Lemma min_embed (rho : nat -> V) (phi : form') : sat I rho (embed phi) <-> sat min_model rho phi.
Proof.
induction phi in rho |- *; try destruct b0; try destruct q; cbn.
1,3-7: firstorder.
erewrite Vector.map_map, Vector.map_ext.
reflexivity.
Admitted.

Lemma embed_subst_t (sigma : nat -> term') (t : term') : embed_t t`[sigma] = (embed_t t)`[sigma >> embed_t].
Proof.
induction t; cbn; trivial.
Admitted.

Lemma embed_subst (sigma : nat -> term') (phi : form') : embed phi[sigma] = (embed phi)[sigma >> embed_t].
Proof.
induction phi in sigma |- *; cbn; trivial.
-
f_equal.
erewrite !Vector.map_map, Vector.map_ext.
reflexivity.
apply embed_subst_t.
-
firstorder congruence.
-
rewrite IHphi.
f_equal.
apply subst_ext.
intros []; cbn; trivial.
unfold funcomp.
cbn.
unfold funcomp.
Admitted.

Lemma embed_sshift n (phi : form') : embed phi[sshift n] = (embed phi)[sshift n].
Proof.
rewrite embed_subst.
apply subst_ext.
Admitted.

Lemma sat_sshift1 (rho : nat -> V) x y (phi : form) : (y .: x .: rho) ⊨ phi[sshift 1] <-> (y .: rho) ⊨ phi.
Proof.
erewrite sat_comp, sat_ext.
reflexivity.
Admitted.

Lemma sat_sshift2 (rho : nat -> V) x y z (phi : form) : (z .: y .: x .: rho) ⊨ phi[sshift 2] <-> (z .: rho) ⊨ phi.
Proof.
erewrite sat_comp, sat_ext.
reflexivity.
Admitted.

Lemma inductive_sat (rho : nat -> V) x : (x .: rho) ⊨ is_inductive $0 -> M_inductive x.
Proof.
cbn.
split.
-
destruct H as [[y Hy] _].
enough (H : ∅ ≡ y).
{
eapply set_equiv_elem; eauto.
now apply set_equiv_equiv.
apply Hy.
}
apply M_ext; trivial; intros z Hz; exfalso; intuition.
now apply M_eset in Hz.
-
intros y [z Hz] % H.
enough (Hx : σ y ≡ z).
{
eapply set_equiv_elem; eauto.
now apply set_equiv_equiv.
apply Hz.
}
apply M_ext; trivial.
+
intros a Ha % sigma_el; trivial.
now apply Hz.
+
intros a Ha % Hz.
Admitted.

Lemma inductive_sat_om (rho : nat -> V) : (ω .: rho) ⊨ is_inductive $0.
Proof.
cbn.
split.
-
exists ∅.
split; try apply M_eset; trivial.
now apply M_om1.
-
intros d Hd.
exists (σ d).
split; try now apply M_om1.
intros d'.
Admitted.

Instance set_equiv_equiv' : Equivalence set_equiv.
Proof.
Admitted.

Instance min_model : interp sig_empty _ V.
Proof.
split.
-
intros [].
-
now apply i_atom.
