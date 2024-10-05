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

Lemma ZF_numeral_trans T n x y : ZFeq' <<= T -> T ⊢ x ∈ tnumeral n ~> y ∈ x ~> y ∈ tnumeral n.
Proof.
intros HT.
induction n; cbn.
-
apply II, Exp.
eapply IE.
apply ZF_eset'.
all: auto.
-
apply bunion_use; trivial.
+
rewrite !imps.
rewrite !imps in IHn.
apply ZF_bunion_el1; auto.
+
apply II.
apply ZF_bunion_el'.
auto.
apply DI1.
eapply ZF_eq_elem; auto.
apply ZF_refl'.
auto.
