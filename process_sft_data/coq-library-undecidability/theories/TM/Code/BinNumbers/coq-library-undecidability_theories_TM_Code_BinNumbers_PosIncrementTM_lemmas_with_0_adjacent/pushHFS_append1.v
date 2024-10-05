From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers PosDefinitions PosPointers PosHelperMachines.
Definition Increment_Step_Rel : pRel sigPos^+ (option unit) 1 := fun tin '(yout, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> match b, yout with | true, None => (* The current symbol is [true]; we simply flip it and repeat the loop *) movedToLeft tout[@Fin0] p false bits | false, Some tt => (* The current symbol is [false]; we flip it (to [true]) and move to the HSB and terminate *) atHSB tout[@Fin0] (append_bits p (true :: bits)) /\ yout = Some tt | _, _ => False end) /\ (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *) atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p false) /\ yout = Some tt).
Definition Increment_Step : pTM sigPos^+ (option unit) 1 := Switch ReadPosSym (fun (s : option bool) => match s with | Some true => Return (SetBitAndMoveLeft false) None (* b = true *) | Some false => Return (SetBitAndMoveLeft true;; GoToHSB) (Some tt) (* b = false *) | None => Return (PushHSB false) (Some tt) (* HSB *) end).
Definition Increment_Loop_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> atHSB tout[@Fin0] (append_bits (Pos.succ (p ~~ b)) bits)) /\ (forall (p : positive), (* If we already are at the HSB, push a 1 and stop *) atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p false)).
Definition Increment_Loop := While Increment_Step.
Definition Increment := GoToLSB_start;; Increment_Loop;; Move Lmove.
Definition Increment_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall (p : positive), tin[@Fin0] ≃ p -> tout[@Fin0] ≃ Pos.succ p.

Lemma pushHFS_append1 bits : pushHSB (append_bits 1 bits) false = append_bits 2 bits.
Proof.
apply Encode_positive_injective.
cbn.
now rewrite !encode_pushHSB, !encode_append_bits; cbn.
