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

Lemma combinations_eq T B C x y : ZFeq' <<= T -> T ⊢ x ≡ enc_stack C -> T ⊢ combinations B x y -> T ⊢ y ≡ enc_stack (derivation_step B C).
Proof.
induction B as [|[s t] B IH] in y, T |-*; cbn; intros HT H1 H2; trivial.
use_exists H2 u.
assert1 H.
use_exists H v.
clear H.
rewrite !combinations_subst, !is_rep_subst.
cbn.
subsimpl.
eapply ZF_trans'.
auto.
eapply CE1.
eapply CE1.
auto.
eapply ZF_trans'.
auto.
2: apply enc_stack_app; auto.
apply ZF_eq_bunion; auto.
-
eapply is_rep_eq; auto.
apply (Weak H1); auto.
eapply CE2.
auto.
-
apply IH; auto.
+
apply (Weak H1); auto.
+
eapply CE2.
eapply CE1.
auto.
