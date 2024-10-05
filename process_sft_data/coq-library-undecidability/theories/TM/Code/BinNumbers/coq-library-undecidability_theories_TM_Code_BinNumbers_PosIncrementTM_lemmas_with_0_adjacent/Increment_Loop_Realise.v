From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers PosDefinitions PosPointers PosHelperMachines.
Definition Increment_Step_Rel : pRel sigPos^+ (option unit) 1 := fun tin '(yout, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> match b, yout with | true, None => (* The current symbol is [true]; we simply flip it and repeat the loop *) movedToLeft tout[@Fin0] p false bits | false, Some tt => (* The current symbol is [false]; we flip it (to [true]) and move to the HSB and terminate *) atHSB tout[@Fin0] (append_bits p (true :: bits)) /\ yout = Some tt | _, _ => False end) /\ (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *) atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p false) /\ yout = Some tt).
Definition Increment_Step : pTM sigPos^+ (option unit) 1 := Switch ReadPosSym (fun (s : option bool) => match s with | Some true => Return (SetBitAndMoveLeft false) None (* b = true *) | Some false => Return (SetBitAndMoveLeft true;; GoToHSB) (Some tt) (* b = false *) | None => Return (PushHSB false) (Some tt) (* HSB *) end).
Definition Increment_Loop_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> atHSB tout[@Fin0] (append_bits (Pos.succ (p ~~ b)) bits)) /\ (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *) atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p false)).
Definition Increment_Loop := While Increment_Step.
Definition Increment := GoToLSB_start;; Increment_Loop;; Move Lmove.
Definition Increment_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall (p : positive), tin[@Fin0] ≃ p -> tout[@Fin0] ≃ Pos.succ p.

Lemma Increment_Loop_Realise : Increment_Loop ⊨ Increment_Loop_Rel.
Proof.
eapply Realise_monotone.
{
unfold Increment_Loop.
TM_Correct.
apply Increment_Step_Realise.
}
{
apply WhileInduction; intros.
{
destruct HLastStep as (HLastStep1&HLastStep2).
cbn in *.
split.
-
intros.
modpon HLastStep1.
destruct b; auto.
TMSimp.
auto.
-
intros.
modpon HLastStep2.
TMSimp.
auto.
}
{
cbn in *.
destruct HLastStep as (HLastStep1&HLastStep2); destruct HStar as (HStar1&HStar2).
split.
-
intros.
modpon HStar1.
destruct b; auto.
destruct p.
+
modpon HLastStep1.
auto.
+
modpon HLastStep1.
auto.
+
modpon HLastStep2.
cbn in *.
now rewrite pushHFS_append2 in HLastStep2.
-
intros.
modpon HStar2.
congruence.
}
}
