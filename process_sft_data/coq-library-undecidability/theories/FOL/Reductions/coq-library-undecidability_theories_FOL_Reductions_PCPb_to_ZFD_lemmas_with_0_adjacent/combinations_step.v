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

Lemma combinations_step B n (i x y : term) : ZFeq' ⊢ i ∈ tnumeral n ~> opair i x ∈ enc_derivations B n ~> combinations B x y ~> opair (σ i) y ∈ enc_derivations B n.
Proof.
induction n; cbn.
-
apply II.
apply Exp.
apply imps.
apply ZF_eset.
-
apply bunion_use; try apply bunion_use; auto.
+
apply II.
apply ZF_bunion_el'.
auto.
apply DI1.
eapply IE.
eapply IE.
eapply IE.
*
eapply Weak.
apply IHn.
auto.
*
auto.
*
auto.
*
auto.
+
apply Exp.
eapply IE.
apply (ZF_numeral_wf (S n)).
auto.
eapply ZF_eq_elem.
auto.
eapply opair_inj1.
auto.
auto.
apply ZF_refl'.
auto.
cbn.
apply ZF_bunion_el'.
auto.
apply DI1.
auto.
+
apply II.
apply ZF_bunion_el'.
auto.
apply DI2.
apply ZF_sing_iff.
auto.
apply ZF_eq_opair.
auto.
*
apply ZF_eq_sig; auto.
*
eapply combinations_eq; auto.
apply enc_derivations_eq.
auto.
eapply ZF_eq_elem; auto; try apply ZF_refl'; auto.
eapply ZF_eq_opair; auto; try apply ZF_refl'.
auto.
+
apply Exp.
eapply IE.
apply (ZF_numeral_wf n).
auto.
eapply ZF_eq_elem.
auto.
apply ZF_refl'.
auto.
eapply ZF_trans'.
auto.
apply ZF_sym'.
auto.
eapply opair_inj1.
auto.
auto.
auto.
apply ZF_sig_el.
auto.
