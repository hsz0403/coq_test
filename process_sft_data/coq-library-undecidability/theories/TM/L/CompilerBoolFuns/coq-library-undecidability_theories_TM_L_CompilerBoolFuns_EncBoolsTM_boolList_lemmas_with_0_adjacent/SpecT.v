From Undecidability.Shared.Libs.PSL Require Import FinTypes Vectors.
From Undecidability.L Require Import L_facts UpToC.
From Coq Require Vector.
Import ListNotations.
From Coq Require Import List.
From Undecidability.TM.L.CompilerBoolFuns Require Import Compiler_spec.
Require Import Equations.Type.DepElim.
From Undecidability.TM Require Import TM_facts Hoare ProgrammingTools.
From Undecidability.TM.Code Require Import CaseBool CaseList WriteValue Copy ListTM.
Set Default Proof Using "Type".
Module Boollist2encBoolsTM.
Section Fix.
Variable Σ : finType.
Variable s b : Σ^+.
Variable (retr_list : Retract (sigList bool) Σ).
Local Instance retr_bool : Retract bool Σ := ComposeRetract retr_list (Retract_sigList_X _).
Definition M__step : pTM (Σ) ^+ (option unit) 3 := If (CaseList _ ⇑ retr_list @ [|Fin0;Fin2|]) (Switch (CaseBool ⇑ retr_bool @ [|Fin2|]) (fun x => WriteMove (if x then s else b) Lmove @ [|Fin1|];; Return Nop None)) (Reset _ @[|Fin0|];;Return (Write b @ [|Fin1|]) (Some tt)).
Definition M__loop := While M__step.
Definition M : pTM (Σ) ^+ unit 3 := (*LiftTapes (MoveToSymbol (fun _ => false) id) [|Fin1|];;*) M__loop.
End Fix.
End Boollist2encBoolsTM.
Module encBoolsTM2boollist.
Section Fix.
Variable Σ : finType.
Variable s b : Σ^+.
Variable (retr_list : Retract (sigList bool) Σ).
Local Instance retr_bool : Retract bool Σ := ComposeRetract retr_list (Retract_sigList_X _).
Definition M__step : pTM (Σ) ^+ (option unit) 2 := Switch (ReadChar @ [|Fin0|]) (fun x => match x with None => Return Nop (Some tt) | Some x => Move Lmove @ [|Fin0|];; If (Relabel (ReadChar @ [|Fin0|]) ssrbool.isSome) ((Cons_constant.M (if Dec (x=s) then true else false)) ⇑ retr_list @ [|Fin1|];;Return Nop (None)) (Return (Move Rmove @ [|Fin0|]) (Some tt)) end).
Definition M__loop := While M__step.
Definition M : pTM (Σ) ^+ unit 2 := (MoveToSymbol (fun _ => false) (fun x => x);;Move Lmove) @ [|Fin0|];; WriteValue (@nil bool)⇑ retr_list @ [|Fin1|];; M__loop.
End Fix.
End encBoolsTM2boollist.

Lemma SpecT (H__neq : s <> b): { f : UpToC (fun bs => length bs + 1) & forall bs, TripleT (≃≃([],[| Custom (eq (encBoolsTM s b bs)); Void|]) ) (f bs) M (fun _ => ≃≃([],[|Custom (eq (encBoolsTM s b bs)) ; Contains _ bs|])) }.
Proof.
evar (f : nat -> nat).
exists_UpToC (fun bs => f (length bs)).
2:now shelve.
unfold M.
intros bs.
hstep.
{
hsteps_cbn.
reflexivity.
}
hnf.
intros _.
hstep.
{
hsteps_cbn.
reflexivity.
}
2:reflexivity.
cbn.
intros _.
{
eapply ConsequenceT.
eapply (projT2 (loop_SpecT H__neq)) with (bs:=_)(res:=_) (tin:=_).
3:reflexivity.
2:{
intro;cbn.
rewrite rev_involutive,app_nil_r.
reflexivity.
}
eapply EntailsI.
intros tin.
unfold encBoolsTM,encBoolsListTM.
rewrite MoveToSymbol_correct_midtape_end.
2:easy.
intros [_ H]%tspecE.
specializeFin H.
destruct H0 as (?&H0&<-).
tspec_solve.
2:rewrite H0;reflexivity.
cbn.
split.
easy.
rewrite <- map_rev,map_map;cbn.
destruct (rev bs);cbn.
all:easy.
}
cbn - ["+"].
rewrite UpToC_le.
ring_simplify.
unfold encBoolsTM,encBoolsListTM.
rewrite MoveToSymbol_steps_midtape_end.
2:easy.
rewrite map_length,rev_length.
[f]:intros n.
now unfold f;set (n:=length bs);reflexivity.
Unshelve.
subst f;cbn beta.
smpl_upToC_solve.
