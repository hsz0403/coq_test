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

Lemma ZF_sub_union T x y : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ sub (⋃ x) (⋃ y).
Proof.
intros HT H.
prv_all z.
apply II.
assert1 H'.
assert (HU : (z ∈ ⋃ x :: T) ⊢ ax_union) by (apply Ctx; firstorder).
apply (AllE x), (AllE z) in HU; cbn in HU; subsimpl_in HU.
apply CE1 in HU.
eapply (IE HU) in H'.
use_exists H' u.
clear H' HU.
eapply ZF_union_el'; auto.
apply CI.
-
eapply ZF_eq_elem.
auto.
apply ZF_refl'; auto.
apply (Weak H); auto.
eapply CE1; auto.
-
eapply CE2; auto.
