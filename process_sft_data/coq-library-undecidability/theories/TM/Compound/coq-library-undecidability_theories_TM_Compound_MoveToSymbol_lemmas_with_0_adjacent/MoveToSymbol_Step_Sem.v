From Undecidability Require Import TM.Util.Prelim.
From Undecidability Require Import TM.Basic.Mono.
From Undecidability Require Import TM.Combinators.Combinators.
From Undecidability Require Import TM.Compound.TMTac.
From Undecidability Require Import TM.Compound.Multi.
From Undecidability Require Import ArithPrelim.
From Coq Require Import FunInd.
From Coq Require Import Recdef.
Set Default Proof Using "Type".
Section MoveToSymbol.
Variable sig : finType.
Variable f : sig -> bool.
Variable g : sig -> sig.
Definition MoveToSymbol_Step : pTM sig (option unit) 1 := Switch (ReadChar) (fun b : option sig => match b with | Some x => if f x (* then Return (Nop) (Some tt) (* found the symbol, break *) *) then Return (Write (g x)) (Some tt) (* found the symbol, break *) else Return (WriteMove (g x) Rmove) (None) (* wrong symbol, move right and continue *) | _ => Return (Nop) (Some tt) (* there is no such symbol, break *) end).
Definition MoveToSymbol_Step_Fun : tape sig -> tape sig := fun t1 => match current t1 with | Some s => if (f s) then tape_write t1 (Some (g s)) else doAct t1 (Some (g s), Rmove) | _ => t1 end.
Definition MoveToSymbol_Step_Rel : Rel (tapes sig 1) (option unit * tapes sig 1) := Mk_R_p (fun tin '(yout, tout) => tout = MoveToSymbol_Step_Fun tin /\ yout = match current tin with | Some m => if f m then Some tt (* break *) else None (* continue *) | _ => (Some tt) (* break *) end ).
Definition MoveToSymbol : pTM sig unit 1 := While MoveToSymbol_Step.
Definition rlength (t : tape sig) := length (tape_local t).
Function MoveToSymbol_Fun (t : tape sig) { measure rlength t } : tape sig := match current t with | Some m => if f m then tape_write t (Some (g m)) else MoveToSymbol_Fun (doAct t (Some (g m), Rmove)) | _ => t end.
Proof.
intros.
cbn.
unfold rlength.
simpl_tape.
destruct t eqn:E; cbn in *; try now inv teq.
lia.
Definition MoveToSymbol_Rel : Rel (tapes sig 1) (unit * tapes sig 1) := Mk_R_p (ignoreParam (fun tin tout => tout = MoveToSymbol_Fun tin)).
Function MoveToSymbol_steps (t : tape sig) { measure rlength t } : nat := match current t with | Some m => if f m then 4 else 4 + (MoveToSymbol_steps (doAct t (Some (g m), Rmove))) | _ => 4 end.
Proof.
intros t m HEq1 HEq2.
cbn.
unfold rlength.
simpl_tape.
destruct t; cbn in *; auto.
all: try now inv HEq1.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Definition MoveToSymbol_L := Mirror MoveToSymbol.
Definition llength (t : tape sig) := length (tape_local_l t).
Function MoveToSymbol_L_Fun (t : tape sig) { measure llength t } : tape sig := match current t with | Some s => if f s then tape_write t (Some (g s)) else MoveToSymbol_L_Fun (doAct t (Some (g s), Lmove)) | _ => t end.
Proof.
intros.
unfold llength.
cbn.
simpl_tape.
destruct t; cbn in *; inv teq.
lia.
Definition MoveToSymbol_L_Rel : Rel (tapes sig 1) (unit * tapes sig 1) := Mk_R_p (ignoreParam (fun tin tout => tout = MoveToSymbol_L_Fun tin)).
Function MoveToSymbol_L_steps (t : tape sig) { measure llength t } : nat := match current t with | Some s => if f s then 4 else 4 + (MoveToSymbol_L_steps (doAct t (Some (g s), Lmove))) | _ => 4 end.
Proof.
intros.
unfold llength.
cbn.
simpl_tape.
destruct t; cbn in *; inv teq.
lia.
End MoveToSymbol.
Ltac smpl_TM_MoveToSymbol := once lazymatch goal with | [ |- MoveToSymbol _ _ ⊨ _ ] => eapply MoveToSymbol_Realise | [ |- MoveToSymbol_L _ _ ⊨ _ ] => eapply MoveToSymbol_L_Realise | [ |- projT1 (MoveToSymbol _ _) ↓ _ ] => eapply MoveToSymbol_Terminates | [ |- projT1 (MoveToSymbol_L _ _) ↓ _ ] => eapply MoveToSymbol_L_Terminates end.
Smpl Add smpl_TM_MoveToSymbol : TM_Correct.
Section MoveToSymbol_Sem.
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Variable sig : finType.
Variable stop : sig -> bool.
Variable f : sig -> sig.
End MoveToSymbol_Sem.

Lemma MoveToSymbol_Step_Sem : MoveToSymbol_Step ⊨c(3) MoveToSymbol_Step_Rel.
Proof.
eapply RealiseIn_monotone.
{
unfold MoveToSymbol_Step.
eapply Switch_RealiseIn.
eapply ReadChar_Sem.
cbn.
instantiate (2 := fun o : option sig => match o with Some x => if f x then _ else _ | None => _ end).
intros [ | ]; cbn.
-
destruct (f e).
+
instantiate (1 := 1).
apply Return_RealiseIn.
eapply Write_Sem.
+
apply Return_RealiseIn.
eapply WriteMove_Sem.
-
apply Return_RealiseIn.
eapply Nop_Sem.
}
{
(cbn; lia).
}
{
unfold MoveToSymbol_Step_Rel, MoveToSymbol_Step_Fun.
intros tin (yout, tout) H.
TMCrush idtac; TMSolve 6.
}
