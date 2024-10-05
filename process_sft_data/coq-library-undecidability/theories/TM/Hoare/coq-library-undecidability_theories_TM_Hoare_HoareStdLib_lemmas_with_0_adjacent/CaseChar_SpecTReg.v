From Undecidability.TM Require Import TMTac.
From Undecidability.TM Require Export Basic.Basic Compound.MoveToSymbol.
From Undecidability.TM.Hoare Require Import HoareLogic HoareCombinators HoareRegister HoareTactics HoareTacticsView.
Ltac hstep_DoAct := lazymatch goal with | [ |- TripleT ?P ?k (DoAct _) ?Q ] => eapply DoAct_SpecTReg | [ |- TripleT ?P ?k (Write _) ?Q ] => eapply DoAct_SpecTReg | [ |- TripleT ?P ?k (WriteMove _ _) ?Q ] => eapply DoAct_SpecTReg | [ |- TripleT ?P ?k (Move _) ?Q ] => eapply DoAct_SpecTReg end.
Smpl Add hstep_DoAct : hstep_Spec.
Ltac hstep_CaseChar := lazymatch goal with | [ |- TripleT ?P ?k (CaseChar _) ?Q ] => eapply CaseChar_SpecTReg | [ |- TripleT ?P ?k ReadChar ?Q ] => refine (_ : TripleT _ _ (CaseChar (fun x => x)) _);eapply CaseChar_SpecTReg end.
Smpl Add hstep_CaseChar : hstep_Spec.
Ltac hstep_MoveToSymbol := lazymatch goal with | [ |- TripleT ?P ?k (MoveToSymbol _ _) ?Q ] => eapply MoveToSymbol_SpecTReg end.
Smpl Add hstep_MoveToSymbol : hstep_Spec.

Lemma CaseChar_SpecTReg (sig F : finType) (f : option (boundary + sig) -> F) P: TripleT ≃≃([],[|Custom P|]) 1 (CaseChar f) (fun y => ≃≃([exists t, y = f (current t) /\ P t],[|Custom (fun t => y = f (current t) /\ P t) |])).
Proof.
eapply RealiseIn_TripleT.
now apply CaseChar_Sem.
cbn.
intros ? ? ? [-> ->] [[] H']%tspecE.
specialize (H' Fin0).
cbn in H'.
eapply tspecI;cbn.
now eauto.
intros i; destruct_fin i.
easy.
