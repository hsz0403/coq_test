From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import EncodeBinNumbers.
From Undecidability Require Import PosDefinitions.
From Undecidability Require Import PosPointers.
From Undecidability Require Import PosHelperMachines.
Local Open Scope positive_scope.
From Undecidability Require Import Compound.Shift.
Definition ShiftLeft_Rel (bit : bool) : pRel sigPos^+ unit 1 := fun tin '(yout, tout) => forall (p : positive), tin[@Fin0] ≃ p -> tout[@Fin0] ≃ p ~~ bit.
Definition ShiftLeft (bit : bool) : pTM sigPos^+ unit 1 := GoToLSB_start;; Shift_L (@isStart _) (bitToSigPos' bit);; Move Lmove;; Write (inl START).
Definition ShiftLeft_num_Step_Rel : pRel sigPos^+ (option unit) 2 := fun tin '(yout, tout) => (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive), atBit tin[@Fin0] px bx bitsx -> tin[@Fin1] ≃ y -> movedToLeft tout[@Fin0] px bx bitsx /\ tout[@Fin1] ≃ y~0 /\ yout = None) /\ (forall (px : positive) (y : positive), atHSB tin[@Fin0] px -> tin[@Fin1] ≃ y -> tout = tin /\ yout = Some tt).
Definition ShiftLeft_num_Step : pTM sigPos^+ (option unit) 2 := Switch (ReadPosSym@[|Fin0|]) (fun (s : option bool) => match s with | Some b => Return (SetBitAndMoveLeft b @[|Fin0|];; ShiftLeft false @[|Fin1|]) None | None => Return Nop (Some tt) end).
Definition ShiftLeft_num_Loop_Rel : pRel sigPos^+ unit 2 := fun tin '(yout, tout) => (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive), atBit tin[@Fin0] px bx bitsx -> tin[@Fin1] ≃ y -> atHSB tout[@Fin0] (append_bits px (bx::bitsx)) /\ tout[@Fin1] ≃ shift_left y (pos_size (px~~bx))) /\ (forall (px : positive) (y : positive), atHSB tin[@Fin0] px -> tin[@Fin1] ≃ y -> tout = tin).
Definition ShiftLeft_num_Loop := While ShiftLeft_num_Step.
Definition ShiftLeft_num : pTM sigPos^+ unit 2 := GoToLSB_start@[|Fin0|];; ShiftLeft_num_Loop;; (Move Lmove)@[|Fin0|].
Definition ShiftLeft_num_Rel : pRel sigPos^+ unit 2 := fun tin '(yout, tout) => forall (p0 : positive) (p1 : positive), tin[@Fin0] ≃ p0 -> tin[@Fin1] ≃ p1 -> tout[@Fin0] ≃ p0 /\ tout[@Fin1] ≃ shift_left p1 (pos_size p0).
Definition IsOne : pTM sigPos^+ bool 1 := Move Rmove;; Move Rmove;; Switch (ReadChar) (fun (c : option sigPos^+) => match c with | Some (inr _) => Return (Move Lmove;; Move Lmove) false | Some (inl _) => Return (Move Lmove;; Move Lmove) true | _ => Return Nop default (* undefined *) end).
Definition IsOne_Rel : pRel sigPos^+ bool 1 := fun tin '(yout, tout) => forall (p : positive), tin[@Fin0] ≃ p -> match yout, p with | true, 1 => tout[@Fin0] ≃ p | false, _~1 => tout[@Fin0] ≃ p | false, _~0 => tout[@Fin0] ≃ p | _, _ => False end.
Definition IsOne_steps : nat := 9.
Definition ShiftRight'_Rel : pRel sigPos^+ unit 1 := fun tin '(yout, tout) => forall (p : positive), p <> 1 -> tin[@Fin0] ≃ p -> tout[@Fin0] ≃ removeLSB p.
Definition ShiftRight' : pTM sigPos^+ unit 1 := Move Rmove;; (* Go to the HSB *) Shift (@isStop _) (inl START);; (* Shift it with a new [START] symbol. This will overwrite [STOP] with the last bit *) Write (inl STOP);; (* Overwrite this last bit with [STOP] again *) MoveLeft _.
Definition ShiftRight_Rel : pRel sigPos^+ unit 1 := fun tin '(yout, tout) => forall (p : positive), tin[@Fin0] ≃ p -> tout[@Fin0] ≃ removeLSB p.
Definition ShiftRight : pTM sigPos^+ unit 1 := If IsOne Nop ShiftRight'.
Definition ShiftRight_num_Step_Rel : pRel sigPos^+ (option unit) 2 := fun tin '(yout, tout) => (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive), atBit tin[@Fin0] px bx bitsx -> tin[@Fin1] ≃ y -> movedToLeft tout[@Fin0] px bx bitsx /\ tout[@Fin1] ≃ removeLSB y /\ yout = None) /\ (forall (px : positive) (y : positive), atHSB tin[@Fin0] px -> tin[@Fin1] ≃ y -> tout = tin /\ yout = Some tt).
Definition ShiftRight_num_Step : pTM sigPos^+ (option unit) 2 := Switch (ReadPosSym@[|Fin0|]) (fun (s : option bool) => match s with | Some b => Return (SetBitAndMoveLeft b @[|Fin0|];; ShiftRight @[|Fin1|]) None | None => Return Nop (Some tt) end).
Definition ShiftRight_num_Loop_Rel : pRel sigPos^+ unit 2 := fun tin '(yout, tout) => (forall (px : positive) (bx : bool) (bitsx : list bool) (y : positive), atBit tin[@Fin0] px bx bitsx -> tin[@Fin1] ≃ y -> atHSB tout[@Fin0] (append_bits px (bx::bitsx)) /\ tout[@Fin1] ≃ shift_right y (pos_size (px~~bx))) /\ (forall (px : positive) (y : positive), atHSB tin[@Fin0] px -> tin[@Fin1] ≃ y -> tout = tin).
Definition ShiftRight_num_Loop := While ShiftRight_num_Step.
Definition ShiftRight_num : pTM sigPos^+ unit 2 := GoToLSB_start@[|Fin0|];; ShiftRight_num_Loop;; (Move Lmove)@[|Fin0|].
Definition ShiftRight_num_Rel : pRel sigPos^+ unit 2 := fun tin '(yout, tout) => forall (p0 : positive) (p1 : positive), tin[@Fin0] ≃ p0 -> tin[@Fin1] ≃ p1 -> tout[@Fin0] ≃ p0 /\ tout[@Fin1] ≃ shift_right p1 (pos_size p0).

Lemma ShiftLeft_Realise (bit : bool) : ShiftLeft bit ⊨ ShiftLeft_Rel bit.
Proof.
eapply Realise_monotone.
{
unfold ShiftLeft.
TM_Correct.
-
apply GoToLSB_start_Realise.
}
{
intros tin ([], tout) H.
intros p Hp.
TMSimp.
simpl_tape.
modpon H.
destruct p; cbn.
-
destruct H as (ls&->).
cbn.
pose proof Encode_positive_startsWith_xH p as (str'&Hstr').
cbn in *.
rewrite Hstr'.
cbn.
simpl_list.
cbn.
rewrite Shift_L_fun_correct_midtape_stop; cbn; auto.
+
hnf.
eexists.
cbn.
simpl_tape.
f_equal.
setoid_rewrite Encode_positive_app_xIO; cbn.
simpl_list; cbn.
rewrite Hstr'.
cbn.
f_equal.
rewrite !map_rev.
simpl_list.
cbn.
rewrite map_id.
auto.
+
intros x (?&<-&?%in_rev)%in_map_iff.
replace str' with (tl (encode_pos p)) in H0 by now rewrite Hstr'.
now pose proof Encode_positive_tl_bits H0 as [-> | ->].
-
destruct H as (ls&->).
cbn.
pose proof Encode_positive_startsWith_xH p as (str'&Hstr').
cbn in *.
rewrite Hstr'.
cbn.
simpl_list.
cbn.
rewrite Shift_L_fun_correct_midtape_stop; cbn; auto.
+
hnf.
eexists.
cbn.
simpl_tape.
f_equal.
setoid_rewrite Encode_positive_app_xIO; cbn.
simpl_list; cbn.
rewrite Hstr'.
cbn.
f_equal.
rewrite !map_rev.
simpl_list.
cbn.
rewrite map_id.
auto.
+
intros x (?&<-&?%in_rev)%in_map_iff.
replace str' with (tl (encode_pos p)) in H0 by now rewrite Hstr'.
now pose proof Encode_positive_tl_bits H0 as [-> | ->].
-
destruct H as (ls&->).
cbn.
do 2 (rewrite Shift_L_fun_equation; cbn).
hnf.
eexists.
f_equal.
cbn.
simpl_tape.
cbn.
now rewrite Encode_positive_app_xIO.
}
