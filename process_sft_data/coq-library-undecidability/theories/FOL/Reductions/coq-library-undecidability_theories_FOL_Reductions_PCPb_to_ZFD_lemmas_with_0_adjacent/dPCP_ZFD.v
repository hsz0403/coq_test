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

Theorem dPCP_ZFD B : dPCPb B -> ZFeq' ⊢ solvable B.
Proof.
intros [s H].
destruct (derivable_derivations H) as [n Hn].
unfold solvable.
apply ExI with (tnumeral n).
cbn.
apply ExI with (enc_derivations B n).
cbn.
apply ExI with (enc_string s).
cbn.
subsimpl.
apply ExI with (enc_stack (derivations B n)).
cbn.
rewrite !enc_stack_subst, !combinations_subst.
cbn.
subsimpl.
repeat apply CI.
-
apply ZF_numeral.
-
prv_all x.
prv_all y.
prv_all z.
apply enc_derivations_functional.
-
apply enc_derivations_base.
-
prv_all x.
prv_all y.
prv_all z.
rewrite !combinations_subst.
cbn.
subsimpl.
apply combinations_step.
-
apply enc_derivations_step.
-
now apply enc_stack_spec.
