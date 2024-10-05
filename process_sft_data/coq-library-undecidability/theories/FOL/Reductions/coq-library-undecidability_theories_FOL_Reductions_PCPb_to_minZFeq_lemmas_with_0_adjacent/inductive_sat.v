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
now apply sigma_el.
