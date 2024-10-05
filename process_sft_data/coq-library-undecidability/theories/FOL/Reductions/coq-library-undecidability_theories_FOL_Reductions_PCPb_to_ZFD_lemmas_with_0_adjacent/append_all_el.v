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

Lemma append_all_el T B s t x y : ZFeq' <<= T -> T ⊢ opair x y ∈ enc_stack B -> T ⊢ opair (prep_string s x) (prep_string t y) ∈ enc_stack (append_all B (s/t)).
Proof.
intros HT H.
induction B as [|[u v] B IH] in T, HT, H |- *; cbn in *.
-
apply Exp.
eapply IE.
2: apply H.
now apply ZF_eset'.
-
eapply (ZF_bunion_el' HT).
eapply DE.
apply (ZF_bunion_inv HT H).
+
apply DI1.
apply IH; auto.
+
assert1 H'.
apply ZF_sing_iff in H'; try now auto.
apply DI2.
apply ZF_sing_iff.
auto.
rewrite !prep_string_app.
apply ZF_eq_opair.
auto.
*
apply ZF_eq_prep.
auto.
eapply opair_inj1; eauto.
*
apply ZF_eq_prep.
auto.
eapply opair_inj2; eauto.
