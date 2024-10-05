From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import BinNumbers.PosDefinitions.
From Undecidability Require Import BinNumbers.PosPointers.
From Undecidability Require Import BinNumbers.PosHelperMachines.
From Undecidability Require Import BinNumbers.PosIncrementTM.
From Undecidability Require Import BinNumbers.PosCompareTM.
From Undecidability Require Import BinNumbers.PosAddTM.
From Undecidability Require Import BinNumbers.PosShiftTM.
Local Open Scope positive_scope.
Fixpoint mult_TR_cont (a : positive) (x y : positive) {struct x} : positive := match x with | x'~1 => mult_TR_cont (a+y) x' (y~0) | x'~0 => mult_TR_cont (a ) x' (y~0) | 1 => a end.
Definition mult_TR (x y : positive) : positive := mult_TR_cont (shift_left y (pos_size x)) x y.
Definition Mult_Step_Rel : pRel sigPos^+ (option unit) 3 := fun tin '(yout, tout) => (forall (px : positive) (bx : bool) (bitsx : list bool) (a y : positive), atBit tin[@Fin0] px bx bitsx -> tin[@Fin1] ≃ y -> tin[@Fin2] ≃ a -> y <= a -> (* We need this to show that we can use [Add'] instead of [Add] *) movedToLeft tout[@Fin0] px bx bitsx /\ tout[@Fin1] ≃ y~0 /\ tout[@Fin2] ≃ (if bx then a+y else a) /\ yout = None) /\ (forall (px : positive) (a y : positive), atHSB tin[@Fin0] px -> tin[@Fin1] ≃ y -> tin[@Fin2] ≃ a -> tout = tin /\ yout = Some tt).
Definition Mult_Step : pTM sigPos^+ (option unit) 3 := Switch (ReadPosSym@[|Fin0|]) (fun (s : option bool) => match s with | Some true => Return (SetBitAndMoveLeft true @[|Fin0|];; Add' @[|Fin1; Fin2|];; ShiftLeft false @[|Fin1|]) None | Some false => Return (SetBitAndMoveLeft false @[|Fin0|];; ShiftLeft false @[|Fin1|]) None | None => Return Nop (Some tt) end).
Definition Mult_Loop_Rel : pRel sigPos^+ unit 3 := fun tin '(_, tout) => (forall (px : positive) (bx : bool) (bitsx : list bool) (a y : positive), atBit tin[@Fin0] px bx bitsx -> tin[@Fin1] ≃ y -> tin[@Fin2] ≃ a -> (pos_size (px~~bx) + pos_size y <= pos_size a) % nat -> (* We need this invariant so that we can use [Add'] instead of [Add] *) atHSB tout[@Fin0] (append_bits px (bx::bitsx)) /\ tout[@Fin1] ≃ shift_left y (pos_size (px ~~ bx)) /\ tout[@Fin2] ≃ mult_TR_cont a (px~~bx) y) /\ (forall (px : positive) (a y : positive), atHSB tin[@Fin0] px -> tin[@Fin1] ≃ y -> tin[@Fin2] ≃ a -> tout = tin).
Definition Mult_Loop : pTM sigPos^+ unit 3 := While Mult_Step.
Definition Mult_Rel : pRel sigPos^+ unit 3 := fun tin '(yout, tout) => forall (x y : positive), tin[@Fin0] ≃ x -> tin[@Fin1] ≃ y -> isVoid tin[@Fin2] -> tout[@Fin0] ≃ x /\ tout[@Fin1] ≃ y /\ tout[@Fin2] ≃ x*y.
Definition Mult : pTM sigPos^+ unit 3 := CopyValue _ @[|Fin1; Fin2|];; ShiftLeft_num @[|Fin0; Fin2|];; GoToLSB_start @[|Fin0|];; Mult_Loop;; Move Lmove @[|Fin0|];; ShiftRight_num @[|Fin0; Fin1|].
Local Arguments mult_TR_cont : simpl never.

Lemma Mult_Loop_Realise : Mult_Loop ⊨ Mult_Loop_Rel.
Proof.
eapply Realise_monotone.
{
unfold Mult_Loop.
TM_Correct.
apply Mult_Step_Realise.
}
{
apply WhileInduction; intros.
{
cbn in *.
destruct HLastStep as (HLastStepA&HLastStepB).
split.
-
intros.
modpon HLastStepA.
{
apply Pos.lt_le_incl.
apply pos_size_lt.
enough ((pos_size y < pos_size px~~bx + pos_size y)%nat) by nia.
rewrite pos_size_append_bit.
nia.
}
congruence.
-
intros.
modpon HLastStepB.
auto.
}
{
cbn in *.
destruct HStar as (HStarA&HStarB).
destruct HLastStep as (HLastStepA&HLastStepB).
split.
-
intros.
rewrite pos_size_append_bit in *.
modpon HStarA.
{
apply Pos.lt_le_incl.
apply pos_size_lt.
enough ((pos_size y < pos_size px~~bx + pos_size y)%nat) by nia.
rewrite pos_size_append_bit.
nia.
}
clear_trivial_eqs.
destruct px; cbn in *.
+
modpon HLastStepA.
{
cbn in *.
destruct bx; cbn.
*
ring_simplify.
ring_simplify in H2.
enough ((pos_size a <= pos_size (a + y))%nat) by nia.
apply pos_size_add_monotone.
*
nia.
}
repeat split; auto.
contains_ext.
f_equal.
cbn.
destruct bx; cbn in *; auto.
+
modpon HLastStepA.
{
cbn in *.
destruct bx; cbn.
*
ring_simplify.
ring_simplify in H2.
enough ((pos_size a <= pos_size (a + y))%nat) by nia.
apply pos_size_add_monotone.
*
nia.
}
repeat split; auto.
contains_ext.
f_equal.
cbn.
destruct bx; cbn in *; auto.
+
modpon HLastStepB.
TMSimp.
repeat split; auto.
contains_ext.
destruct bx; auto.
-
intros.
modpon HStarB.
TMSimp.
}
}
