From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList CaseSum Hoare.
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.
Set Default Proof Using "Type".
Section Rev.
Variable (sig sigX : finType) (X : Type) (cX : codable sigX X).
Definition Rev_Step : pTM (sigList sigX)^+ (option unit) 3 := If (CaseList _ @[|Fin0;Fin2|]) (Return (Constr_cons _ @[|Fin1; Fin2|];; Reset _ @[|Fin2|]) None) (Return (ResetEmpty1 _ @[|Fin0|]) (Some tt)).
Definition Rev_Step_size (xs : list X) := match xs with | nil => [| ResetEmpty1_size; id; id |] | x :: xs' => [| CaseList_size0 x; Constr_cons_size x; CaseList_size1 x >> Reset_size x |] end.
Definition Rev_Step_Rel : pRel (sigList sigX)^+ (option unit) 3 := fun tin '(yout, tout) => forall (xs ys : list X) (sx sy sz : nat), let size := Rev_Step_size xs in tin[@Fin0] ≃(;sx) xs -> tin[@Fin1] ≃(;sy) ys -> isVoid_size tin[@Fin2] sz -> match yout, xs with | (Some tt), nil => isVoid_size tout[@Fin0] (size@>Fin0 sx) /\ tout[@Fin1] ≃(;size@>Fin1 sy) ys /\ isVoid_size tout[@Fin2] (size@>Fin2 sz) | None, x :: xs' => tout[@Fin0] ≃(;size@>Fin0 sx) xs' /\ tout[@Fin1] ≃(;size@>Fin1 sy) x :: ys /\ isVoid_size tout[@Fin2] (size@>Fin2 sz) | _, _ => False end.
Definition Rev_Step_steps (xs : list X) : nat := match xs with | nil => 1 + CaseList_steps xs + ResetEmpty1_steps | x :: xs' => 2 + CaseList_steps xs + Constr_cons_steps x + Reset_steps x end.
Definition Rev_Step_T : tRel (sigList sigX)^+ 3 := fun tin k => exists (xs ys : list X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ isVoid tin[@Fin2] /\ Rev_Step_steps xs <= k.
Definition Rev_Append := While Rev_Step.
Fixpoint Rev_Append_size (xs : list X) : Vector.t (nat->nat) 3 := match xs with | nil => Rev_Step_size xs | x :: xs' => Rev_Step_size xs >>> Rev_Append_size xs' end.
Definition Rev_Append_Rel : pRel (sigList sigX)^+ unit 3 := fun tin '(yout, tout) => forall (xs ys : list X) (sx sy sz : nat), let size := Rev_Append_size xs in tin[@Fin0] ≃(;sx) xs -> tin[@Fin1] ≃(;sy) ys -> isVoid_size tin[@Fin2] sz -> isVoid_size tout[@Fin0] (size@>Fin0 sx) /\ tout[@Fin1] ≃(;size@>Fin1 sy) rev xs ++ ys /\ isVoid_size tout[@Fin2] (size@>Fin2 sz).
Fixpoint Rev_Append_steps (xs : list X) : nat := match xs with | nil => Rev_Step_steps xs | x :: xs' => 1 + Rev_Step_steps xs + Rev_Append_steps xs' end.
Definition Rev_Append_T : tRel (sigList sigX)^+ 3 := fun tin k => exists (xs ys : list X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ isVoid tin[@Fin2] /\ Rev_Append_steps xs <= k.
Definition Rev := Constr_nil _ @[|Fin1|];; Rev_Append.
Definition Rev_size (xs : list X) := [| Rev_Append_size xs @>Fin0; pred >> Rev_Append_size xs @>Fin1; Rev_Append_size xs @>Fin2 |].
Definition Rev_Rel : pRel (sigList sigX)^+ unit 3 := fun tin '(yout, tout) => forall (xs : list X) (s0 s1 s2 : nat), let size := Rev_size xs in tin[@Fin0] ≃(;s0) xs -> isVoid_size tin[@Fin1] s1 -> isVoid_size tin[@Fin2] s2 -> isVoid_size tout[@Fin0] (size@>Fin0 s0) /\ tout[@Fin1] ≃(;size@>Fin1 s1) rev xs /\ isVoid_size tout[@Fin2] (size@>Fin2 s2).
Definition Rev_steps (xs : list X) := 1 + Constr_nil_steps + Rev_Append_steps xs.
Definition Rev_T : tRel (sigList sigX)^+ 3 := fun tin k => exists (xs : list X), tin[@Fin0] ≃ xs /\ isVoid tin[@Fin1] /\ isVoid tin[@Fin2] /\ Rev_steps xs <= k.
End Rev.
Import Hoare.
Ltac hstep_App := lazymatch goal with | [ |- TripleT ?P ?k (Rev _) ?Q ] => eapply Rev_SpecT | [ |- TripleT ?P ?k (Rev_Append _) ?Q ] => refine (Rev_Append_SpecT _ _ _ _);shelve end.
Smpl Add hstep_App : hstep_Spec.

Lemma Rev_Realise : Rev ⊨ Rev_Rel.
Proof.
eapply Realise_monotone.
{
unfold Rev.
TM_Correct.
-
apply Rev_Append_Realise.
}
{
intros tin ([], tout) H.
TMSimp.
intros.
modpon H.
modpon H0.
repeat split; auto.
contains_ext.
now simpl_list.
}
