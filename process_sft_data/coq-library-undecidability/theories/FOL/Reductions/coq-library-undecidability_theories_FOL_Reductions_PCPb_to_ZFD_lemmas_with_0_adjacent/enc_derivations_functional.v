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

Lemma enc_derivations_functional B n x y y' : ZFeq' ⊢ opair x y ∈ enc_derivations B n ~> opair x y' ∈ enc_derivations B n ~> y ≡ y'.
Proof.
induction n; cbn -[derivations].
-
repeat apply II.
eapply opair_inj2.
auto.
eapply ZF_trans'.
auto.
+
apply ZF_sing_iff; auto.
+
apply ZF_sym'.
auto.
apply ZF_sing_iff; auto.
-
apply bunion_use; try apply bunion_use.
1,2,5: auto.
+
repeat rewrite <- imps.
now apply (Weak IHn).
+
apply Exp.
eapply IE.
apply (@ZF_numeral_wf _ (S n)).
auto.
eapply ZF_derivations_bound.
auto.
eapply ZF_eq_elem.
auto.
2: apply ZF_refl'; auto.
2: auto.
apply ZF_eq_opair; auto.
eapply opair_inj1; auto.
apply ZF_refl'.
auto.
+
apply Exp.
eapply IE.
apply (@ZF_numeral_wf _ (S n)).
auto.
eapply ZF_derivations_bound.
auto.
eapply ZF_eq_elem.
auto.
2: apply ZF_refl'; auto.
2: auto.
apply ZF_eq_opair; auto.
eapply opair_inj1; auto.
apply ZF_refl'.
auto.
+
eapply opair_inj2.
auto.
eapply ZF_trans'; auto.
apply ZF_sym'; auto.
