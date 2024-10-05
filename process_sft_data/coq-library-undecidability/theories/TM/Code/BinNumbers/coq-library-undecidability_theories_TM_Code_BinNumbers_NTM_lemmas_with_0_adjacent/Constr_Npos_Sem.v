From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import Code.CaseSum.
From Undecidability Require Import ArithPrelim.
From Coq Require Import BinNums.
Local Open Scope N_scope.
Definition WriteNumber (n : N) : pTM sigN^+ unit 1 := WriteValue n.
Definition WriteNumber_Rel (n : N) : pRel sigN^+ unit 1:= fun tin '(_, tout) => isVoid tin[@Fin0] -> tout[@Fin0] ≃ n.
Definition WriteNumber_steps (n : N) : nat := 2 * Encode_N_size n + 3.
Definition Constr_N0 : pTM sigN^+ unit 1 := WriteNumber 0.
Definition Constr_N0_Rel : pRel sigN^+ unit 1:= fun tin '(_, tout) => isVoid tin[@Fin0] -> tout[@Fin0] ≃ 0.
Definition Constr_N0_steps : nat := Eval cbn in WriteNumber_steps 0.
Definition Constr_Npos : pTM sigN^+ unit 1 := Constr_Some _.
Definition Constr_Npos_Rel : pRel sigN^+ unit 1 := fun tin '(_, tout) => forall (x : positive), tin[@Fin0] ≃ x -> tout[@Fin0] ≃ Npos x.
Definition Constr_Npos_Sem : Constr_Npos ⊨c(Constr_Some_steps) Constr_Npos_Rel.
Proof.
eapply RealiseIn_monotone.
{
unfold Constr_Npos.
TM_Correct.
}
{
reflexivity.
}
{
intros tin ([], tout) H.
cbn in *.
intros x Hx.
modpon H.
auto.
}
Definition CaseN : pTM sigN^+ bool 1 := If (CaseOption _) (Return Nop true) (Return (WriteNumber 0) false).
Definition CaseN_Rel : pRel sigN^+ bool 1 := fun tin '(yout, tout) => forall (x : N), tin[@Fin0] ≃ x -> match yout, x with | true, Npos p => tout[@Fin0] ≃ p | false, N0 => tout[@Fin0] ≃ 0 | _, _ => False end.
Definition CaseN_steps : nat := 13.
From Undecidability Require Import PosIncrementTM.
Definition Increment_N : pTM sigN^+ unit 1 := If (CaseOption _) (Increment ⇑ _;; Constr_Some _) (WriteNumber 1).
Definition Increment_N_Rel : pRel sigN^+ unit 1 := fun tin '(_, tout) => forall (n : BinNums.N), tin[@Fin0] ≃ n -> tout[@Fin0] ≃ N.succ n.
From Undecidability Require Import PosAddTM.
Definition Add'_N : pTM sigN^+ unit 2 := If (CaseOption _ @[|Fin0|]) (If (CaseOption _ @[|Fin1|]) (Add' ⇑ _;; Constr_Some _@[|Fin0|];; Constr_Some _@[|Fin1|]) (Constr_Some _@[|Fin0|];; CopyValue _)) (Constr_None _@[|Fin0|]).
Definition Add'_N_Rel : pRel sigN^+ unit 2 := fun tin '(_, tout) => forall (x y : N), tin[@Fin0] ≃ x -> tin[@Fin1] ≃ y -> x <= y -> tout[@Fin0] ≃ x /\ tout[@Fin1] ≃ x + y.
Definition Add_N : pTM sigN^+ unit 3 := If (CaseOption _ @[|Fin0|]) (If (CaseOption _ @[|Fin1|]) (Add ⇑ _;; Constr_Some _@[|Fin0|];; Constr_Some _@[|Fin1|];; Constr_Some _@[|Fin2|]) (Constr_Some _@[|Fin0|];; Constr_None _@[|Fin1|];; CopyValue _ @[|Fin0; Fin2|])) (Constr_None _@[|Fin0|];; CopyValue _@[|Fin1; Fin2|]).
Definition Add_N_Rel : pRel sigN^+ unit 3 := fun tin '(_, tout) => forall (x y : N), tin[@Fin0] ≃ x -> tin[@Fin1] ≃ y -> isVoid tin[@Fin2] -> tout[@Fin0] ≃ x /\ tout[@Fin1] ≃ y /\ tout[@Fin2] ≃ x+y.
From Undecidability Require Import PosMultTM.
Definition Mult_N : pTM sigN^+ unit 3 := If (CaseN @[|Fin0|]) (If (CaseN @[|Fin1|]) (Mult ⇑ _;; Constr_Npos @[|Fin0|];; Constr_Npos @[|Fin1|];; Constr_Npos @[|Fin2|]) (Constr_Npos @[|Fin0|];; Constr_N0 @[|Fin2|])) (Constr_N0 @[|Fin2|]).
Definition Mult_N_Rel : pRel sigN^+ unit 3 := fun tin '(yout, tout) => forall (x y : N), tin[@Fin0] ≃ x -> tin[@Fin1] ≃ y -> isVoid tin[@Fin2] -> tout[@Fin0] ≃ x /\ tout[@Fin1] ≃ y /\ tout[@Fin2] ≃ x*y.
Ltac smpl_TM_NTM := match goal with (* WriteNumber *) | [ |- WriteNumber _ ⊨ _ ] => eapply RealiseIn_Realise; apply WriteNumber_Sem | [ |- WriteNumber _ ⊨c(_) _ ] => apply WriteNumber_Sem | [ |- projT1 (WriteNumber _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply WriteNumber_Sem (* Constr_N0 *) | [ |- Constr_N0 ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_N0_Sem | [ |- Constr_N0 ⊨c(_) _ ] => apply Constr_N0_Sem | [ |- projT1 (Constr_N0) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_N0_Sem (* Constr_Npos *) | [ |- Constr_Npos ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_Npos_Sem | [ |- Constr_Npos ⊨c(_) _ ] => apply Constr_Npos_Sem | [ |- projT1 (Constr_Npos) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_Npos_Sem (* CaseN *) | [ |- CaseN ⊨ _ ] => eapply RealiseIn_Realise; apply CaseN_Sem | [ |- CaseN ⊨c(_) _ ] => apply CaseN_Sem | [ |- projT1 (CaseN) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply CaseN_Sem (* Increment_N *) | [ |- Increment_N ⊨ _ ] => apply Increment_N_Realise (* Add'_N *) | [ |- Add'_N ⊨ _ ] => apply Add'_N_Realise (* Add_N *) | [ |- Add_N ⊨ _ ] => apply Add_N_Realise (* Mult_N *) | [ |- Mult_N ⊨ _ ] => apply Mult_N_Realise end.
Smpl Add smpl_TM_NTM : TM_Correct.

Definition Constr_Npos_Sem : Constr_Npos ⊨c(Constr_Some_steps) Constr_Npos_Rel.
Proof.
eapply RealiseIn_monotone.
{
unfold Constr_Npos.
TM_Correct.
}
{
reflexivity.
}
{
intros tin ([], tout) H.
cbn in *.
intros x Hx.
modpon H.
auto.
}
