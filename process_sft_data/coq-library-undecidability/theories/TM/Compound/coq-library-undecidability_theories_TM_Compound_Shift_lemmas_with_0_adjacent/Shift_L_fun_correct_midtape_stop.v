From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac.
From Undecidability Require Import TM.Compound.Multi.
From Coq Require Import FunInd.
From Coq Require Import Recdef.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Section Shift.
Variable sig : finType.
Variable (f : sig -> bool).
Definition Shift_Step_Rel (s : sig) : pRel sig (sig + unit) 1 := fun tin '(yout, tout) => match current tin[@Fin0] with | Some c => if f c then tout[@Fin0] = doAct tin[@Fin0] (Some s, Nmove) /\ yout = inr tt else tout[@Fin0] = doAct tin[@Fin0] (Some s, Rmove) /\ yout = inl c | None => tout[@Fin0] = tape_write tin[@Fin0] (Some s) /\ yout = inr tt end.
Definition Shift_Step (s : sig) : pTM sig (sig + unit) 1 := Switch (ReadChar) (fun c => match c with | Some c => if f c then Return (Write s) (inr tt) else Return (WriteMove s Rmove) (inl c) | None => Return (Write s) (inr tt) end).
Definition Shift := StateWhile Shift_Step.
Definition Shift_fun_measure (t : tape sig) := length (tape_local t).
Function Shift_fun (s : sig) (t : tape sig) {measure Shift_fun_measure t} := match current t with | Some c => if f c then doAct t (Some s, Nmove) else Shift_fun c (doAct t (Some s, Rmove)) | None => tape_write t (Some s) end.
Proof.
intros.
destruct t; cbn in *; inv teq.
unfold Shift_fun_measure.
simpl_tape.
lia.
Definition Shift_Rel (s : sig) : pRel sig unit 1 := ignoreParam (fun tin tout => tout[@Fin0] = Shift_fun s tin[@Fin0]).
Fixpoint Shift_steps (rs : list sig) := match rs with | nil => 4 | c :: rs => if f c then 4 else 4 + Shift_steps rs end.
Definition Shift_L (s : sig) := Mirror (Shift s).
Definition Shift_L_fun_measure (t : tape sig) := length (tape_local_l t).
Function Shift_L_fun (s : sig) (t : tape sig) {measure Shift_L_fun_measure t} := match current t with | Some c => if f c then doAct t (Some s, Nmove) else Shift_L_fun c (doAct t (Some s, Lmove)) | None => tape_write t (Some s) end.
Proof.
intros.
destruct t; cbn in *; inv teq.
unfold Shift_L_fun_measure.
simpl_tape.
lia.
Definition Shift_L_Rel (s : sig) : pRel sig unit 1 := ignoreParam (fun tin tout => tout[@Fin0] = Shift_L_fun s tin[@Fin0]).
End Shift.
Ltac smpl_TM_Shift := once lazymatch goal with | [ |- Shift _ _ ⊨ _ ] => eapply Shift_Realise | [ |- Shift_L _ _ ⊨ _ ] => eapply Shift_L_Realise | [ |- projT1 (Shift _ _) ↓ _ ] => eapply Shift_TerminatesIn | [ |- projT1 (Shift_L _ _) ↓ _ ] => eapply Shift_L_TerminatesIn end.
Smpl Add smpl_TM_Shift : TM_Correct.

Lemma Shift_L_fun_correct_midtape_stop s ls m rs l h ls' : f m = false -> f l = false -> f h = true -> (forall x, In x ls -> f x = false) -> Shift_L_fun s (midtape (ls ++ l :: h :: ls') m rs) = midtape ls' l (rev ls ++ m :: s :: rs).
Proof.
revert s rs m.
induction ls as [ | l' ls IH]; intros; cbn in *.
-
do 3 (rewrite Shift_L_fun_equation; cbn).
rewrite H, H0, H1.
reflexivity.
-
do 1 (rewrite Shift_L_fun_equation; cbn).
rewrite <- !app_assoc.
cbn.
rewrite H.
rewrite IH; eauto.
