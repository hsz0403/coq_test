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

Lemma is_rep_eq T B s t x y : ZFeq' <<= T -> T ⊢ x ≡ enc_stack B -> T ⊢ is_rep (comb_rel s t) x y -> T ⊢ y ≡ enc_stack (append_all B (s / t)).
Proof.
intros HT H1 H2.
apply ZF_ext'; trivial.
-
prv_all a.
apply (AllE a) in H2.
cbn in H2.
subsimpl_in H2.
eapply CE1 in H2.
rewrite imps in *.
use_exists H2 z.
assert1 H.
apply CE in H as [H H'].
unfold comb_rel at 2 in H'.
cbn in H'.
subsimpl_in H'.
rewrite !prep_string_subst in H'.
cbn in H'.
use_exists H' c.
clear H'.
cbn.
subsimpl.
rewrite !prep_string_subst.
cbn.
assert1 H'.
use_exists H' d.
clear H'.
cbn.
subsimpl.
rewrite !prep_string_subst.
cbn.
subsimpl.
eapply ZF_eq_elem.
auto.
apply ZF_sym'.
auto.
eapply CE2.
auto.
apply ZF_refl'.
auto.
apply append_all_el.
auto.
eapply ZF_eq_elem.
auto.
eapply CE1.
auto.
eapply (Weak H1).
auto.
eapply (Weak H).
auto.
-
prv_all a.
apply (AllE a) in H2.
cbn in H2.
subsimpl_in H2.
eapply CE2 in H2.
apply II.
eapply IE; try apply (Weak H2).
auto.
induction B as [|[u v] B IH] in T, x, HT, H1 |- *; cbn in *.
+
apply Exp.
eapply IE.
apply ZF_eset'.
all: auto.
+
rewrite <- imps.
apply bunion_use; trivial.
*
specialize (IH T (enc_stack B) HT).
assert (H : T ⊢ enc_stack B ≡ enc_stack B) by now apply ZF_refl'.
apply IH in H.
use_exists H z.
clear H.
apply ExI with z.
cbn.
subsimpl.
assert1 H.
apply CE in H as [H H'].
apply CI; trivial.
eapply ZF_eq_elem.
auto.
apply ZF_refl'.
auto.
apply ZF_sym'.
auto.
apply (Weak H1).
auto.
apply ZF_bunion_el1; trivial.
auto.
*
apply ExI with (opair (enc_string u) (enc_string v)).
cbn.
subsimpl.
apply CI.
--
eapply ZF_eq_elem.
auto.
apply ZF_refl'.
auto.
apply ZF_sym'.
auto.
apply (Weak H1).
auto.
apply ZF_bunion_el2.
auto.
eapply Weak.
apply ZF_sing_el.
auto.
--
cbn.
apply ExI with (enc_string v).
cbn.
apply ExI with (enc_string u).
cbn.
subsimpl.
rewrite !prep_string_subst, !prep_string_app; cbn.
subsimpl.
apply CI; auto.
apply ZF_refl'.
auto.
