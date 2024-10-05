From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers PosDefinitions PosPointers.
From Undecidability Require Import TM.Basic.Duo.
Local Open Scope positive_scope.
Definition ReadPosSym : pTM sigPos^+ (option bool) 1 := CaseChar (fun (s : option sigPos^+) => match s with | Some (inr sigPos_xH) => None | Some (inr sigPos_xO) => Some false | Some (inr sigPos_xI) => Some true | _ => default end).
Definition ReadPosSym_Rel : pRel sigPos^+ (option bool) 1 := fun tin '(yout, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> match yout, b with | Some false, false => tout = tin | Some true, true => tout = tin | _, _ => False end) /\ (forall (p : positive), atHSB tin[@Fin0] p -> tout = tin /\ yout = None).
Definition ReadPosSym2 : pTM sigPos^+ (option bool * option bool) 2 := CaseChar2 (fun (s1 s2 : option sigPos^+) => (match s1 with | Some (inr sigPos_xH) => None | Some (inr sigPos_xO) => Some false | Some (inr sigPos_xI) => Some true | _ => default end, match s2 with | Some (inr sigPos_xH) => None | Some (inr sigPos_xO) => Some false | Some (inr sigPos_xI) => Some true | _ => default end)).
Definition ReadPosSym2_Rel : pRel sigPos^+ (option bool * option bool) 2 := fun tin '(yout, tout) => (forall (p1 : positive) (b1 : bool) (bits1 : list bool) (p2 : positive) (b2 : bool) (bits2 : list bool), atBit tin[@Fin0] p1 b1 bits1 -> atBit tin[@Fin1] p2 b2 bits2 -> match yout, b1, b2 with | (Some false, Some false), false, false => tout = tin | (Some false, Some true), false, true => tout = tin | (Some true, Some false), true, false => tout = tin | (Some true, Some true), true, true => tout = tin | _, _, _ => False end) /\ (forall (p1 : positive) (b1 : bool) (bits1 : list bool) (p2 : positive), atBit tin[@Fin0] p1 b1 bits1 -> atHSB tin[@Fin1] p2 -> match yout, b1 with | (Some false, None), false => tout = tin | (Some true, None), true => tout = tin | _, _ => False end) /\ (forall (p1 : positive) (p2 : positive) (b2 : bool) (bits2 : list bool), atHSB tin[@Fin0] p1 -> atBit tin[@Fin1] p2 b2 bits2 -> match yout, b2 with | (None, Some false), false => tout = tin | (None, Some true), true => tout = tin | _, _ => False end) /\ (forall (p1 p2 : positive), atHSB tin[@Fin0] p1 -> atHSB tin[@Fin1] p2 -> tout = tin /\ yout = (None, None)).
Definition isxH (s : sigPos) := match s with sigPos_xH => true | _ => false end.
Definition isxH' (s : sigPos^+) := match s with inr s => isxH s | _ => false end.
Definition GoToHSB : pTM sigPos^+ unit 1 := MoveToSymbol_L isxH' id.
Definition GoToHSB_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => (forall (p : positive) (b : bool) (bits : list bool), atBit tin[@Fin0] p b bits -> atHSB tout[@Fin0] (append_bits p (b :: bits))) /\ (forall (p : positive), (* If we already are at the HSB, do nothing *) atHSB tin[@Fin0] p -> atHSB tout[@Fin0] p).
Definition GoToLSB_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall (p : positive), atHSB tin[@Fin0] p -> match p with | p' ~ 0 => atLSB tout[@Fin0] p' false | p' ~ 1 => atLSB tout[@Fin0] p' true | 1 => atHSB tout[@Fin0] p end.
Definition GoToLSB : pTM sigPos^+ unit 1 := MoveRight _;; Move Lmove.
Definition GoToLSB_start : pTM sigPos^+ unit 1 := Move Rmove;; GoToLSB.
Definition GoToLSB_start_Rel : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall (p : positive), tin[@Fin0] ≃ p -> match p with | p' ~ 1 => atLSB tout[@Fin0] p' true | p' ~ 0 => atLSB tout[@Fin0] p' false | 1 => atHSB tout[@Fin0] p end.
Definition movedToLeft (t : tape sigPos^+) (p : positive) (b : bool) (bits : list bool) := match p with | p'~1 => atBit t p' true (b :: bits) | p'~0 => atBit t p' false (b :: bits) | xH => atHSB t (append_bits p (b :: bits)) end.
Definition SetBitAndMoveLeft_Rel (b : bool) : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall (p : positive) (b' : bool) (bits : list bool), atBit tin[@Fin0] p b' bits -> movedToLeft tout[@Fin0] p b bits.
Definition SetBitAndMoveLeft (b : bool) : pTM sigPos^+ unit 1 := WriteMove (bitToSigPos' b) Lmove.
Definition PushHSB_Rel (b : bool) : pRel sigPos^+ unit 1 := fun tin '(_, tout) => forall p, atHSB tin[@Fin0] p -> atHSB tout[@Fin0] (pushHSB p b).
Definition PushHSB (b : bool) : pTM sigPos^+ unit 1 := WriteMove (bitToSigPos' b) Lmove;; WriteMove (inr sigPos_xH) Lmove;; WriteMove (inl START) Rmove.
Definition PushHSB_steps : nat := 5.

Lemma PushHSB_Sem (b : bool) : PushHSB b ⊨c(PushHSB_steps) PushHSB_Rel b.
Proof.
eapply RealiseIn_monotone.
{
unfold PushHSB.
TM_Correct.
}
{
reflexivity.
}
{
intros tin ([], tout) H.
TMSimp.
destruct H2 as (ls&->).
hnf; cbn.
pose proof Encode_positive_startsWith_xH p as (str'&Hstr').
repeat setoid_rewrite Hstr'.
cbn.
rewrite !encode_pushHSB; cbn.
destruct ls; cbn.
+
exists nil.
f_equal.
f_equal.
f_equal.
now setoid_rewrite Hstr'.
+
exists ls.
f_equal.
f_equal.
f_equal.
now setoid_rewrite Hstr'.
}
