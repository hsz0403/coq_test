From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import BinNumbers.PosDefinitions.
From Undecidability Require Import BinNumbers.PosPointers.
From Undecidability Require Import BinNumbers.PosHelperMachines.
From Undecidability Require Import BinNumbers.PosIncrementTM.
From Undecidability Require Import BinNumbers.PosCompareTM.
Local Open Scope positive_scope.
Fixpoint addTR_rec (a : list bool) (x y : positive) : list bool := match x, y with | p~1, q~1 => addTR_rec_carry (false :: a) p q | p~1, q~0 => addTR_rec (true :: a) p q | p~1, 1 => pos_to_bits (Pos.succ p) ++ false :: a | p~0, q~1 => addTR_rec (true :: a) p q | p~0, q~0 => addTR_rec (false :: a) p q | p~0, 1 => pos_to_bits p ++ true :: a | 1, q~1 => pos_to_bits (Pos.succ q) ++ false :: a | 1, q~0 => pos_to_bits q ++ true :: a | 1, 1 => false :: a end with addTR_rec_carry (a : list bool) (x y : positive) : list bool := match x, y with | p~1, q~1 => addTR_rec_carry (true :: a) p q | p~1, q~0 => addTR_rec_carry (false :: a) p q | p~1, 1 => pos_to_bits (Pos.succ p) ++ true :: a | p~0, q~1 => addTR_rec_carry (false :: a) p q | p~0, q~0 => addTR_rec (true :: a) p q | p~0, 1 => pos_to_bits (Pos.succ p) ++ false :: a | 1, q~1 => pos_to_bits (Pos.succ q) ++ true :: a | 1, q~0 => pos_to_bits (Pos.succ q) ++ false :: a | 1, 1 => true :: a end.
Definition addTR_rec' (carry : bool) (a : list bool) (x y : positive) : list bool := if carry then addTR_rec_carry a x y else addTR_rec a x y.
Definition addTR (x y : positive) := bits_to_pos (addTR_rec nil x y).
Definition fullAdder (x y c : bool) : bool*bool := (xorb (xorb x y) c, (x && y) || (x && c) || (y && c)).
Definition add_baseCase (b carry : bool) (p : positive) := if (b || carry) then (Pos.succ p) ~~ (negb (xorb b carry)) else p ~~ (negb (xorb b carry)).
Definition Add_BaseCase_Rel (carry : bool) (b : bool) : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall (p : positive) (bits : list bool), atBit tin[@Fin0] p b bits -> atHSB tout[@Fin0] (append_bits (add_baseCase b carry p) bits).
Definition Add_BaseCase (carry : bool) (b : bool) : pTM sigPos^+ unit 1 := if (b || carry) then SetBitAndMoveLeft (negb (xorb b carry));; Increment_Loop else SetBitAndMoveLeft (negb (xorb b carry));; GoToHSB.
Definition Add_Step_Rel (carry : bool) : pRel sigPos^+ (bool+unit) 2 := fun tin '(yout, tout) => (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive) (b1 : bool) (bits1 : list bool), atBit tin[@Fin0] p0 b0 bits0 -> atBit tin[@Fin1] p1 b1 bits1 -> (* Pos.le (p0 ~~ b0) (p1 ~~ b1) -> *) movedToLeft tout[@Fin0] p0 b0 bits0 /\ movedToLeft tout[@Fin1] p1 (fst (fullAdder b0 b1 carry)) bits1 /\ yout = inl (snd (fullAdder b0 b1 carry))) /\ (forall (p0 : positive) (p1 : positive) (b1 : bool) (bits1 : list bool), atHSB tin[@Fin0] p0 -> atBit tin[@Fin1] p1 b1 bits1 -> atHSB tout[@Fin0] p0 /\ atHSB tout[@Fin1] (append_bits (add_baseCase b1 carry p1) bits1) /\ yout = inr tt) /\ (forall (p0 : positive) (p1 : positive), atHSB tin[@Fin0] p0 -> atHSB tin[@Fin1] p1 -> atHSB tout[@Fin0] p0 /\ atHSB tout[@Fin1] (pushHSB p1 carry) /\ yout = inr tt).
Definition Add_Step (carry : bool) : pTM sigPos^+ (bool+unit) 2 := Switch (ReadPosSym2) (fun '(s0, s1) => match s0, s1 with | Some b0, Some b1 => Return (SetBitAndMoveLeft b0 @ [|Fin0|];; SetBitAndMoveLeft (fst (fullAdder b0 b1 carry)) @ [|Fin1|]) (inl (snd (fullAdder b0 b1 carry))) | None, Some b1 => Return ((Add_BaseCase carry b1)@[|Fin1|]) (inr tt) | None, None => Return (PushHSB carry @[|Fin1|]) (inr tt) | Some b0, None => Return Nop default (* not specified *) end).
Definition Add_Loop_Rel (carry : bool) : pRel sigPos^+ unit 2 := fun tin '(_, tout) => (forall (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive) (b1 : bool) (bits1 : list bool), atBit tin[@Fin0] p0 b0 bits0 -> atBit tin[@Fin1] p1 b1 bits1 -> Pos.le (p0 ~~ b0) (p1 ~~ b1) -> atHSB tout[@Fin0] (append_bits p0 (b0 :: bits0)) /\ atHSB tout[@Fin1] (bits_to_pos (addTR_rec' carry bits1 (p0 ~~ b0) (p1 ~~ b1)))) /\ (forall (p0 : positive) (p1 : positive) (b1 : bool) (bits1 : list bool), atHSB tin[@Fin0] p0 -> atBit tin[@Fin1] p1 b1 bits1 -> atHSB tout[@Fin0] p0 /\ atHSB tout[@Fin1] (append_bits (add_baseCase b1 carry p1) bits1)) /\ (forall (p0 : positive) (p1 : positive), atHSB tin[@Fin0] p0 -> atHSB tin[@Fin1] p1 -> atHSB tout[@Fin0] p0 /\ atHSB tout[@Fin1] (pushHSB p1 carry)).
Definition Add_Loop : bool -> pTM sigPos^+ unit 2 := StateWhile Add_Step.
Definition Add' : pTM sigPos^+ unit 2 := GoToLSB_start@[|Fin0|];; GoToLSB_start@[|Fin1|];; (Add_Loop false)@[|Fin0; Fin1|];; (Move Lmove)@[|Fin0|];; (Move Lmove)@[|Fin1|].
Definition Add'_Rel : pRel sigPos^+ unit 2 := fun tin '(_, tout) => forall (p0 p1 : positive), tin[@Fin0] ≃ p0 -> tin[@Fin1] ≃ p1 -> p0 <= p1 -> tout[@Fin0] ≃ p0 /\ tout[@Fin1] ≃ p0 + p1.
Definition Add : pTM sigPos^+ unit 3 := Switch Max (fun (c : comparison) => match c with | Gt => Add' @[|Fin1; Fin2|] | _ => Add' @[|Fin0; Fin2|] end).
Definition Add_Rel : pRel sigPos^+ unit 3 := fun tin '(_, tout) => forall (p0 p1 : positive), tin[@Fin0] ≃ p0 -> tin[@Fin1] ≃ p1 -> isVoid tin[@Fin2] -> tout[@Fin0] ≃ p0 /\ tout[@Fin1] ≃ p1 /\ tout[@Fin2] ≃ p0 + p1.
Definition Add_onto : pTM sigPos^+ unit 3 := Add;; MoveValue _ @[|Fin2; Fin1|].
Definition Add_onto_Rel : pRel sigPos^+ unit 3 := fun tin '(_, tout) => forall (p0 p1 : positive), tin[@Fin0] ≃ p0 -> tin[@Fin1] ≃ p1 -> isVoid tin[@Fin2] -> tout[@Fin0] ≃ p0 /\ tout[@Fin1] ≃ p0 + p1 /\ isVoid tout[@Fin2].

Lemma Add'_Realise : Add' ⊨ Add'_Rel.
Proof.
eapply Realise_monotone.
{
unfold Add'.
TM_Correct.
-
apply GoToLSB_start_Realise.
-
apply GoToLSB_start_Realise.
-
apply Add_Loop_Realise.
}
{
intros tin ([], tout) H.
intros p0 p1 Hp0 Hp1 HRight.
TMSimp.
rename H into HGoToHSB, H0 into HGoToHSB', H2 into HLoopA, H6 into HLoopB, H7 into HLoopC.
modpon HGoToHSB.
modpon HGoToHSB'.
destruct p0; destruct p1; try nia.
-
modpon HLoopA; cbn in *.
repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
rewrite (proj2 (@addTR_rec_correct _ _ _)) in HLoopA0.
rewrite bits_to_pos_cons in HLoopA0.
now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
-
modpon HLoopA; cbn in *.
repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
rewrite (proj1 (@addTR_rec_correct _ _ _)) in HLoopA0.
rewrite bits_to_pos_cons in HLoopA0.
now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
-
modpon HLoopA; cbn in *.
repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
rewrite (proj1 (@addTR_rec_correct _ _ _)) in HLoopA0.
rewrite bits_to_pos_cons in HLoopA0.
now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
-
modpon HLoopA; cbn in *.
repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
rewrite (proj1 (@addTR_rec_correct _ _ _)) in HLoopA0.
rewrite bits_to_pos_cons in HLoopA0.
now setoid_rewrite pos_to_bits_to_pos in HLoopA0.
-
modpon HLoopB; cbn in *.
repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
-
modpon HLoopB; cbn in *.
repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
-
modpon HLoopC; cbn in *.
repeat split; eauto; apply atHSB_moveLeft_contains; eauto.
}
