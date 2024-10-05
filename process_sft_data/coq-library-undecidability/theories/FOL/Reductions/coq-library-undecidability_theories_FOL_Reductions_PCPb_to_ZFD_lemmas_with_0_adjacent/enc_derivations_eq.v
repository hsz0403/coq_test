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

Lemma enc_derivations_eq T B n x : ZFeq' <<= T -> T ⊢ opair (tnumeral n) x ∈ enc_derivations B n -> T ⊢ x ≡ enc_stack (derivations B n).
Proof.
intros HT H.
destruct n; cbn in *.
-
eapply opair_inj2; trivial.
eapply ZF_sing_iff; eauto.
-
apply ZF_bunion_inv in H; trivial.
apply (DE H).
+
apply Exp.
eapply IE.
apply (ZF_numeral_wf (S n)).
auto.
eapply ZF_derivations_bound.
auto.
auto.
+
eapply opair_inj2.
auto.
apply ZF_sing_iff.
auto.
auto.
