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

Lemma opair_inj2 T x y x' y' : ZFeq' <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ y ≡ y'.
Proof.
intros HT H.
assert (H' : T ⊢ y ≡ x' ∨ y ≡ y').
-
assert (H2 : T ⊢ {x; y} ∈ opair x' y').
{
eapply ZF_eq_elem; trivial.
apply ZF_refl'; trivial.
apply H.
apply ZF_pair_el'; trivial.
apply DI2.
now apply ZF_refl'.
}
apply ZF_pair_el' in H2; trivial.
apply (DE H2).
+
apply DI1.
apply ZF_sym'; auto.
eapply sing_pair2; auto.
apply ZF_sym'; auto.
+
apply ZF_pair_el'; auto.
eapply ZF_eq_elem; auto.
*
apply ZF_refl'; auto.
*
apply ZF_pair_el'; auto.
apply DI2.
apply ZF_refl'.
auto.
-
apply (DE H'); try apply prv_T1.
assert (H1 : T ⊢ x ≡ x') by apply (opair_inj1 HT H).
assert (H2 : T ⊢ {x'; y'} ∈ opair x y).
{
eapply ZF_eq_elem; trivial.
apply ZF_refl'; trivial.
apply ZF_sym', H; trivial.
apply ZF_pair_el'; trivial.
apply DI2.
now apply ZF_refl'.
}
apply ZF_pair_el' in H2; trivial.
eapply DE; try eapply (Weak H2); auto.
+
eapply ZF_trans'; auto.
eapply ZF_trans'; auto.
*
apply ZF_sym'.
auto.
apply (Weak H1).
auto.
*
eapply sing_pair2; auto.
apply ZF_sym'; auto.
+
eapply ZF_trans'; auto.
eapply sing_pair2; auto.
eapply ZF_trans'; auto.
2: apply ZF_sym'; auto.
eapply ZF_eq_pair; try apply ZF_sym'; auto.
apply (Weak H1).
auto.
+
auto.
