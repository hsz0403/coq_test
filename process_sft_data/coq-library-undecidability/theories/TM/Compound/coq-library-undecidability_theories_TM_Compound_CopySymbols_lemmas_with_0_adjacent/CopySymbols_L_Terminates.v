From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac TM.Compound.Multi.
From Undecidability Require Import TM.Lifting.LiftTapes.
From Coq Require Import FunInd.
From Coq Require Import Recdef.
Section CopySymbols.
Variable sig : finType.
Variable f : sig -> bool.
Definition CopySymbols_Step : pTM sig (option unit) 2 := Switch (ReadChar_at Fin0) (fun b : option sig => match b with | Some x => (* First write the read symbol to tape 1 *) if f x then (* found the symbol: write it to tape 1; break and return *) Return (LiftTapes (Write x) [|Fin1|]) (Some tt) else (* wrong symbol: write it to tape 1 and move both tapes right and continue *) Return (LiftTapes (Write x) [|Fin1|];; MovePar Rmove Rmove) (None) | _ => Return Nop (Some tt) (* there is no such symbol, break and return *) end).
Definition CopySymbols_Step_Rel : pRel sig (option unit) 2 := fun tin '(yout, tout) => match current tin[@Fin0] with | Some x => if (f x) then tout[@Fin0] = tin[@Fin0] /\ tout[@Fin1] = tape_write tin[@Fin1] (Some x) /\ yout = Some tt (* break *) else tout[@Fin0] = tape_move_right tin[@Fin0] /\ tout[@Fin1] = doAct tin[@Fin1] (Some x, Rmove) /\ yout = None (* continue *) | _ => tout = tin /\ yout = Some tt end.
Definition CopySymbols : pTM sig unit 2 := While CopySymbols_Step.
Definition rlength (t : tape sig) := length (tape_local t).
Definition rlength' (tin : tape sig * tape sig) : nat := rlength (fst tin).
Function CopySymbols_Fun (tin : tape sig * tape sig) { measure rlength' tin } : tape sig * tape sig := match current (fst tin) with | Some s => if f s then (fst tin, tape_write (snd tin) (Some s)) else CopySymbols_Fun (tape_move_right (fst tin), doAct (snd tin) (Some s, Rmove)) | _ => tin end.
Proof.
intros (t1,t2) m HC Hs.
unfold rlength', rlength.
cbn.
destruct t1; cbn in *; inv HC.
simpl_tape.
lia.
Definition CopySymbols_Rel : Rel (tapes sig 2) (unit * tapes sig 2) := ignoreParam (fun tin tout => (tout[@Fin0], tout[@Fin1]) = CopySymbols_Fun (tin[@Fin0], tin[@Fin1])).
Function CopySymbols_steps (t : tape sig) { measure rlength t } : nat := match current t with | Some m => if f m then 8 else 8 + CopySymbols_steps (tape_move_right t) | _ => 8 end.
Proof.
intros tin m HC Hs.
unfold rlength', rlength.
cbn.
destruct tin; cbn in *; inv HC.
simpl_tape.
lia.
Definition CopySymbols_L := Mirror CopySymbols.
Definition llength (t : tape sig) := length (tape_local_l t).
Definition llength' (tin : tape sig * tape sig) : nat := llength (fst tin).
Function CopySymbols_L_Fun (tin : tape sig * tape sig) { measure llength' tin } : tape sig * tape sig := match current (fst tin) with | Some s => if f s then (fst tin, tape_write (snd tin) (Some s)) else CopySymbols_L_Fun (tape_move_left (fst tin), doAct (snd tin) (Some s, Lmove)) | _ => tin end.
Proof.
intros (t1,t2) m HC Hs.
unfold llength', llength.
cbn.
destruct t1; cbn in *; inv HC.
simpl_tape.
lia.
Definition CopySymbols_L_Rel : Rel (tapes sig 2) (unit * tapes sig 2) := ignoreParam (fun tin tout => (tout[@Fin0], tout[@Fin1]) = CopySymbols_L_Fun (tin[@Fin0], tin[@Fin1])).
Function CopySymbols_L_steps (t : tape sig) { measure llength t } : nat := match current t with | Some s => if f s then 8 else 8 + CopySymbols_L_steps (tape_move_left t) | _ => 8 end.
Proof.
intros tin m HC Hs.
unfold llength', llength.
cbn.
destruct tin; cbn in *; inv HC.
simpl_tape.
lia.
End CopySymbols.
Ltac smpl_TM_CopySymbols := once lazymatch goal with | [ |- CopySymbols _ ⊨ _ ] => eapply CopySymbols_Realise | [ |- projT1 (CopySymbols _) ↓ _ ] => eapply CopySymbols_Terminates | [ |- CopySymbols_L _ ⊨ _ ] => eapply CopySymbols_L_Realise | [ |- projT1 (CopySymbols_L _) ↓ _ ] => eapply CopySymbols_L_Terminates end.
Smpl Add smpl_TM_CopySymbols : TM_Correct.

Lemma CopySymbols_L_Terminates : projT1 CopySymbols_L ↓ (fun tin k => CopySymbols_L_steps (tin[@Fin0]) <= k).
Proof.
eapply TerminatesIn_monotone.
-
eapply Mirror_Terminates.
eapply CopySymbols_Terminates.
-
cbn.
intros tin k Hk.
destruct_tapes; cbn.
rewrite <- Hk.
unfold mirror_tapes.
rewrite CopySymbols_steps_mirror.
cbn.
auto.
