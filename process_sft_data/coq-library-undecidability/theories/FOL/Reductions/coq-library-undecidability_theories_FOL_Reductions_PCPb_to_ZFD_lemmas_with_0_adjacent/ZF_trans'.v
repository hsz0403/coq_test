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

Lemma ZF_trans' T x y z : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ z -> T ⊢ x ≡ z.
Proof.
intros H1 H2 H3.
eapply IE; try apply H3.
eapply IE; try apply H2.
assert (H : T ⊢ ax_trans) by (apply Ctx; firstorder).
now apply (AllE x), (AllE y), (AllE z) in H; cbn in H; subsimpl_in H.
