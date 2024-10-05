Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction_facts.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Reductions.PCPb_to_ZF.
From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Local Definition BSRS := list(card bool).
Local Notation "x / y" := (x, y).
Section ZF.
Context { p : peirce }.
Close Scope sem.
Fixpoint tnumeral n := match n with | O => ∅ | S n => σ (tnumeral n) end.
Definition sing x := {x; x}.
Fixpoint enc_derivations B n := match n with | O => sing (opair ∅ (enc_stack B)) | S n => enc_derivations B n ∪ sing (opair (tnumeral (S n)) (enc_stack (derivations B (S n)))) end.
Local Arguments comb_rel : simpl never.
Local Arguments is_rep : simpl never.
End ZF.

Lemma ZF_derivations_bound T B k n x : ZFeq' <<= T -> T ⊢ opair k x ∈ enc_derivations B n -> T ⊢ k ∈ σ (tnumeral n).
Proof.
induction n in T |- *; cbn; intros HT H.
-
apply ZF_sing_iff in H; trivial.
eapply ZF_eq_elem; trivial.
apply ZF_sym'; trivial.
eapply opair_inj1; trivial.
apply H.
apply ZF_refl'; trivial.
eapply ZF_bunion_el'; trivial.
apply DI2.
apply ZF_sing_iff; trivial.
apply ZF_refl'; trivial.
-
apply ZF_bunion_inv in H; trivial.
apply (DE H).
+
apply ZF_bunion_el1.
auto.
apply IHn; auto.
+
apply ZF_bunion_el2.
auto.
apply ZF_sing_iff.
auto.
eapply opair_inj1.
auto.
apply ZF_sing_iff; auto.
