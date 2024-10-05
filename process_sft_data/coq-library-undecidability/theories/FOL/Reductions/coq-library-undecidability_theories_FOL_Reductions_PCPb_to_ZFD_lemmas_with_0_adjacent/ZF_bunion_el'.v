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

Lemma ZF_bunion_el' T x y z : ZFeq' <<= T -> T ⊢ (z ∈ x ∨ z ∈ y) -> T ⊢ z ∈ x ∪ y.
Proof.
intros HT H.
apply (DE H).
-
eapply ZF_union_el' with x.
auto.
apply CI; auto.
apply ZF_pair_el'.
auto.
apply DI1.
apply ZF_refl'.
auto.
-
eapply ZF_union_el' with y.
auto.
apply CI; auto.
apply ZF_pair_el'.
auto.
apply DI2.
apply ZF_refl'.
auto.
