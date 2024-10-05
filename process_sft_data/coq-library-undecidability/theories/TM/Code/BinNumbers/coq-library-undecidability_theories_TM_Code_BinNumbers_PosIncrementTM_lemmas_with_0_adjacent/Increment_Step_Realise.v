From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers PosDefinitions PosPointers PosHelperMachines.
Definition Increment_Step_Rel : pRel sigPos^+ (option unit) 1 := fun tin '(yout, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> match b, yout with | true, None => (* The current symbol is [true]; we simply flip it and repeat the loop *) movedToLeft tout[@Fin0] p false bits | false, Some tt => (* The current symbol is [false]; we flip it (to [true]) and move to the HSB and terminate *) atHSB tout[@Fin0] (append_bits p (true :: bits)) /\ yout = Some tt | _, _ => False end) /\ (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *) atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p false) /\ yout = Some tt).
Definition Increment_Step : pTM sigPos^+ (option unit) 1 := Switch ReadPosSym (fun (s : option bool) => match s with | Some true => Return (SetBitAndMoveLeft false) None (* b = true *) | Some false => Return (SetBitAndMoveLeft true;; GoToHSB) (Some tt) (* b = false *) | None => Return (PushHSB false) (Some tt) (* HSB *) end).
Definition Increment_Loop_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> atHSB tout[@Fin0] (append_bits (Pos.succ (p ~~ b)) bits)) /\ (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *) atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p false)).
Definition Increment_Loop := While Increment_Step.
Definition Increment := GoToLSB_start;; Increment_Loop;; Move Lmove.
Definition Increment_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall (p : positive), tin[@Fin0] ≃ p -> tout[@Fin0] ≃ Pos.succ p.

Lemma Increment_Step_Realise : Increment_Step ⊨ Increment_Step_Rel.
Proof.
eapply Realise_monotone.
{
unfold Increment_Step.
TM_Correct.
-
eapply RealiseIn_Realise.
apply ReadPosSym_Sem.
-
eapply RealiseIn_Realise.
apply SetBitAndMoveLeft_Sem.
-
eapply RealiseIn_Realise.
apply SetBitAndMoveLeft_Sem.
-
apply GoToHSB_Realise.
-
eapply RealiseIn_Realise.
apply PushHSB_Sem.
}
{
intros tin (yout, tout) H.
TMSimp.
split; TMSimp.
{
rename H into HRead, H1 into HRead', H0 into HSwitch.
clear HRead'.
intros p b bits HatBits.
specialize HRead with (1 := HatBits).
destruct ymid as [ [ (* b=true *) | (* b=false *) ] | (* not the case *) ]; cbn in *; auto.
{
destruct b; auto; subst.
TMSimp.
modpon H2.
eauto.
}
{
destruct b; auto; subst.
TMSimp.
split; auto.
specialize H2 with (1 := HatBits).
destruct p; eauto.
-
modpon H3.
eauto.
-
modpon H3.
eauto.
}
}
{
intros p HatHSB.
specialize H1 with (1 := HatHSB) as ([= ->]&->).
cbn in H0.
TMSimp.
split; eauto.
}
}
