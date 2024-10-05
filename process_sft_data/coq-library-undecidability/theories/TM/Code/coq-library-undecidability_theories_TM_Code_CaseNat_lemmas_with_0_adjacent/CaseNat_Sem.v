From Undecidability.TM.Code Require Import ProgrammingTools.
Hint Rewrite tl_length : list.
Section CaseNat.
Definition CaseNat_Rel : Rel (tapes sigNat^+ 1) (bool * tapes sigNat^+ 1) := Mk_R_p (fun tin '(yout, tout) => forall (n : nat) (sn : nat), tin ≃(;sn) n -> match yout, n with | false, O => tout ≃(;sn) 0 | true, S n' => tout ≃(;S sn) n' | _, _ => False end).
Definition CaseNat : pTM sigNat^+ bool 1 := Move Rmove;; Switch (ReadChar) (fun o => match o with | Some (inr sigNat_S) => Return (Write (inl START)) true (* S *) | Some (inr sigNat_O) => Return (Move Lmove) false (* O *) | _ => Return (Nop) default (* invalid input *) end).
Definition CaseNat_steps := 5.
Section NatConstructor.
Definition S_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) := Mk_R_p (ignoreParam (fun tin tout => forall n sn : nat, tin ≃(;sn) n -> tout ≃(;pred sn) S n)).
Definition Constr_S : pTM sigNat^+ unit 1 := WriteMove (inr sigNat_S) Lmove;; Write (inl START).
Definition Constr_S_steps := 3.
Definition Constr_O_size := pred >> pred.
Definition O_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) := fun tin '(_, tout) => forall sn, isVoid_size tin[@Fin0] sn -> tout[@Fin0] ≃(;Constr_O_size sn) O.
Definition Constr_O : pTM sigNat^+ unit 1 := WriteValue 0.
Goal Constr_O = WriteMove (inl STOP) Lmove;; WriteMove (inr sigNat_O) Lmove;; Write (inl START).
Proof.
unfold Constr_O, WriteValue, WriteString.WriteString, encode, Encode_map, map, rev, Encode_nat, encode, repeat, app.
reflexivity.
Definition Constr_O_steps := 5.
End NatConstructor.
End CaseNat.
Ltac smpl_TM_CaseNat := once lazymatch goal with | [ |- CaseNat ⊨ _ ] => eapply RealiseIn_Realise; apply CaseNat_Sem | [ |- CaseNat ⊨c(_) _ ] => apply CaseNat_Sem | [ |- projT1 (CaseNat) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply CaseNat_Sem | [ |- Constr_O ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_O_Sem | [ |- Constr_O ⊨c(_) _ ] => apply Constr_O_Sem | [ |- projT1 (Constr_O) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_O_Sem | [ |- Constr_S ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_S_Sem | [ |- Constr_S ⊨c(_) _ ] => apply Constr_S_Sem | [ |- projT1 (Constr_S) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_S_Sem end.
Smpl Add smpl_TM_CaseNat : TM_Correct.
From Undecidability.TM.Hoare Require Import HoareLogic HoareRegister HoareTactics.
Definition CaseNat_size (n : nat) : Vector.t (nat->nat) 1 := match n with | O => [|id|] | S n' => [|S|] end.
Ltac hstep_Nat := lazymatch goal with | [ |- TripleT ?P ?k Constr_O ?Q ] => eapply Constr_O_SpecT_size | [ |- TripleT ?P ?k Constr_S ?Q ] => eapply Constr_S_SpecT_size | [ |- TripleT ?P ?k CaseNat ?Q ] => eapply CaseNat_SpecT_size end.
Smpl Add hstep_Nat : hstep_Spec.

Lemma CaseNat_Sem : CaseNat ⊨c(CaseNat_steps) CaseNat_Rel.
Proof.
unfold CaseNat_steps.
eapply RealiseIn_monotone.
{
unfold CaseNat.
TM_Correct.
}
{
Unshelve.
4,8: reflexivity.
all: lia.
}
{
intros tin (yout&tout) H.
intros n s HEncN.
TMSimp.
destruct HEncN as (r1&HEncN&Hs).
TMSimp.
destruct n; cbn in *; TMSimp.
-
repeat econstructor; auto.
-
hnf.
eexists.
split.
f_equal.
cbn.
lia.
}
