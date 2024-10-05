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

Lemma opair_inj1 T x y x' y' : ZFeq' <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ x ≡ x'.
Proof.
intros HT He.
assert (H : T ⊢ {x; x} ∈ opair x y).
{
apply ZF_pair_el'; trivial.
apply DI1.
now apply ZF_refl'.
}
eapply ZF_eq_elem in H; try apply He; try apply ZF_refl'; trivial.
apply ZF_pair_el' in H; trivial.
apply (DE H); eapply sing_pair1; try apply prv_T1; auto.
