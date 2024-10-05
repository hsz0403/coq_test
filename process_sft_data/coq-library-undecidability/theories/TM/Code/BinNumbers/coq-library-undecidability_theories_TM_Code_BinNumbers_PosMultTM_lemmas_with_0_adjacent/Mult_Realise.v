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

Lemma Mult_Realise : Mult ⊨ Mult_Rel.
Proof.
eapply Realise_monotone.
{
unfold Mult.
TM_Correct.
-
apply ShiftLeft_num_Realise.
-
apply GoToLSB_start_Realise.
-
apply Mult_Loop_Realise.
-
apply ShiftRight_num_Realise.
}
{
intros tin ([], tout) H.
hnf; intros x y Hx Hy Hright.
TMSimp.
rename H into HCopyValue, H0 into HShiftLeft, H2 into HGoToLSB, H4 into HLoopA, H7 into HLoopB, H8 into HShiftRight.
modpon HCopyValue.
modpon HShiftLeft.
modpon HGoToLSB.
destruct x; cbn -[shift_left shift_right mult_TR_cont] in *.
-
modpon HLoopA; cbn -[shift_left shift_right mult_TR_cont]in *.
{
rewrite pos_size_shift_left.
nia.
}
modpon HShiftRight; [ apply atHSB_moveLeft_contains; eauto | ].
repeat split; eauto using atHSB_moveLeft_contains.
+
contains_ext; f_equal.
now rewrite shift_left_shift_right.
+
contains_ext; f_equal.
change (S (pos_size x)) with (pos_size (x~1)).
rewrite (proj1 (mult_TR_cont_correct 42 (x~1) y)).
nia.
-
modpon HLoopA; cbn -[shift_left shift_right mult_TR_cont]in *.
{
rewrite pos_size_shift_left.
nia.
}
modpon HShiftRight; [ apply atHSB_moveLeft_contains; eauto | ].
repeat split; eauto using atHSB_moveLeft_contains.
+
contains_ext; f_equal.
now rewrite shift_left_shift_right.
+
contains_ext; f_equal.
change (S (pos_size x)) with (pos_size (x~0)).
rewrite (proj1 (mult_TR_cont_correct 42 (x~0) y)).
nia.
-
modpon HLoopB.
TMSimp.
modpon HShiftRight; [ apply atHSB_moveLeft_contains; eauto | ].
TMSimp.
repeat split; eauto using atHSB_moveLeft_contains.
}
