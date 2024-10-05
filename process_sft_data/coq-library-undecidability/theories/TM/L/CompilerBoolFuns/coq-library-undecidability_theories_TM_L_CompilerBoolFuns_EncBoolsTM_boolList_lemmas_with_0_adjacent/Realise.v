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

Theorem Realise (H__neq : s <> b): Realise M (fun t '(r, t') => forall (l : list bool), t[@Fin0] = encBoolsTM s b l -> isVoid t[@Fin1] -> t[@Fin0] = t'[@Fin0] /\ t'[@Fin1] ≃ l).
Proof.
repeat (eapply RealiseIntroAll;intro).
eapply Realise_monotone.
-
eapply TripleT_Realise,(projT2 (SpecT H__neq)).
-
intros ? [] H **.
modpon H.
{
unfold "≃≃",withSpace;cbn.
intros i; destruct_fin i;cbn.
all:eauto.
}
repeat destruct _;unfold "≃≃",withSpace in H;cbn in H.
specializeFin H.
cbn in *;easy.
