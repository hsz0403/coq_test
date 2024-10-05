From Undecidability.TM Require Import ProgrammingTools.
Require Import Undecidability.Shared.Libs.PSL.Bijection.
From Undecidability Require Import Basic.Duo.
From Undecidability Require Import Code.CaseFin Code.CaseList Code.CasePair.
From Undecidability Require Import TM.Univ.LookupAssociativeListTM.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Definition map_pair (X X' Y Y' : Type) (f : X -> X') (g : Y -> Y') : X*Y->X'*Y' := fun '(x,y) => (f x, g y).
Section Graph.
Variable (A : finType) (B : Type) (f : A -> B).
Set Default Proof Using "Type".
Definition graph_of_fun : list (A*B) := map (fun x => (x, f x)) enum.
End Graph.
Notation sigState := (sigPair bool sigNat).
Section Univ.
Variable (sigM : finType).
Notation sigGraph := (sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option sigM * move) sigState))).
Variable (sig : finType).
Variable (retr_sigGraph_sig : Retract sigGraph sig).
Variable (retr_sigTape_sig : Retract sigM sig).
Local Definition retr_sigCurrentStateNumber_sigGraph : Retract sigNat sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_sigPair_Y _ _))).
Local Definition retr_sigCurrentStateNumber_sig : Retract sigNat sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentStateNumber_sigGraph.
Local Definition retr_sigCurrentState_sigGraph : Retract sigState sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_id _))).
Local Definition retr_sigCurrentState_sig : Retract sigState sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentState_sigGraph.
Local Definition retr_sigCurrentStateFinal_sigGraph : Retract bool sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_Y _ (Retract_sigPair_X _ _))).
Local Definition retr_sigCurrentStateFinal_sig : Retract bool sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentStateFinal_sigGraph.
Local Definition retr_sigNextState_sigGraph : Retract sigState sigGraph := Retract_sigList_X (Retract_sigPair_Y _ _).
Local Definition retr_sigNextState_sig : Retract sigState sig := ComposeRetract retr_sigGraph_sig retr_sigNextState_sigGraph.
Local Definition retr_sigCurrentSymbol_sigGraph : Retract (option sigM) sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_sigPair_X _ _)).
Local Definition retr_sigCurrentSymbol_sig: Retract (option sigM) sig := ComposeRetract retr_sigGraph_sig retr_sigCurrentSymbol_sigGraph.
Local Definition retr_act_sigGraph : Retract (option sigM * move) sigGraph := _.
Local Definition retr_act_sig : Retract (option sigM * move) sig := ComposeRetract retr_sigGraph_sig retr_act_sigGraph.
Local Definition retr_key_sigGraph : Retract _ sigGraph := Retract_sigList_X (Retract_sigPair_X _ (Retract_id _)).
Local Definition retr_key_sig : Retract _ sig := ComposeRetract retr_sigGraph_sig retr_key_sigGraph.
Local Definition retr_value_sigGraph : Retract _ sigGraph := Retract_sigList_X (Retract_sigPair_Y _ (Retract_id _)).
Local Definition retr_value_sig : Retract _ sig := ComposeRetract retr_sigGraph_sig retr_value_sigGraph.
Definition containsWorkingTape (t : tape sig^+) (tp : tape sigM) := t = mapTape (fun s => inr (Retr_f (Retract := retr_sigTape_sig) s)) tp.
Definition ReadCurrent : pTM sig^+ (option sigM) 1 := CaseChar (fun c => match c with | Some (inr c') => match Retr_g (Retract := retr_sigTape_sig) c' with | Some s => Some s | None => None end | _ => None end).
Definition ReadCurrent_Rel : pRel sig^+ (option sigM) 1 := fun tin '(yout, tout) => forall tp, containsWorkingTape tin[@Fin0] tp -> containsWorkingTape tout[@Fin0] tp /\ yout = current tp.
Local Instance Encode_optSigM : codable (option sigM) (option sigM) := Encode_Finite _.
Definition ReadCurrent' : pTM sig^+ unit 2 := Switch (ReadCurrent @ [|Fin0|]) (fun c => WriteValue c ⇑ retr_sigCurrentSymbol_sig @ [|Fin1|]).
Definition ReadCurrent_size := pred >> pred.
Definition ReadCurrent'_Rel : pRel sig^+ unit 2 := ignoreParam( fun tin tout => forall (tp : tape sigM) (s : nat), containsWorkingTape tin[@Fin0] tp -> isVoid_size tin[@Fin1] s -> containsWorkingTape tout[@Fin0] tp /\ tout[@Fin1] ≃(retr_sigCurrentSymbol_sig; ReadCurrent_size s) current tp).
Definition ReadCurrent'_steps := 7.
Definition DoAction : option sigM * move -> pTM sig^+ unit 1 := fun '(m, w) => DoAct (map_opt (fun s => inr (Retr_f s)) m, w).
Definition DoAction_Rel (a : option sigM * move) : pRel sig^+ unit 1 := ignoreParam (fun tin tout => forall tp, containsWorkingTape tin[@Fin0] tp -> containsWorkingTape tout[@Fin0] (doAct tp a)).
Definition DoAction' : pTM sig^+ unit 2 := Switch (CaseFin (FinType(EqType(option sigM * move))) ⇑ retr_act_sig @ [|Fin1|]) (fun a => DoAction a @ [|Fin0|]).
Local Instance Encode_action : codable (option sigM * move) (option sigM * move) := Encode_Finite _.
Definition DoAction_size (a : option sigM * move) (s : nat) := (Reset_size a s).
Definition DoAction'_Rel : pRel sig^+ unit 2 := ignoreParam (fun tin tout => forall (tp : tape sigM) (a : option sigM * move) (s : nat), let size := DoAction_size a in containsWorkingTape tin[@Fin0] tp -> tin[@Fin1] ≃(retr_act_sig; s) a -> containsWorkingTape tout[@Fin0] (doAct tp a) /\ isVoid_size tout[@Fin1] (size s)).
Definition DoAction'_steps := 7.
Definition SetFinal (final : bool) : pTM sig^+ unit 2 := WriteValue final ⇑ retr_sigCurrentStateFinal_sig @ [|Fin1|];; Constr_pair (FinType(EqType bool)) (FinType(EqType sigNat)) ⇑ retr_sigCurrentState_sig @ [|Fin1; Fin0|];; ResetEmpty1 _ @ [|Fin1|].
Definition SetFinal_size : Vector.t (nat->nat) 2 := [| Constr_pair_size true; WriteValue_size true >> ResetEmpty1_size |].
Definition SetFinal_Rel (final : bool) : pRel sig^+ unit 2 := ignoreParam (fun tin tout => forall (q : nat) (s0 s1 : nat), tin[@Fin0] ≃(retr_sigCurrentStateNumber_sig; s0) q -> isVoid_size tin[@Fin1] s1 -> tout[@Fin0] ≃(retr_sigCurrentState_sig; SetFinal_size@>Fin0 s0) (final, q) /\ isVoid_size tout[@Fin1] (SetFinal_size@>Fin1 s1)).
Definition SetFinal_steps := 2 + WriteValue_steps 1 + Constr_pair_steps true + ResetEmpty1_steps.
Definition SetFinal_T : tRel sig^+ 2 := fun tin k => exists (q:nat), tin[@Fin0] ≃(retr_sigCurrentStateNumber_sig) q /\ isVoid tin[@Fin1] /\ SetFinal_steps <= k.
Definition containsState (t : tape sig^+) (M : TM sigM 1) (q : state M) := t ≃(retr_sigCurrentState_sig) (halt q, index q).
Definition containsState_size (t : tape sig^+) (M : TM sigM 1) (q : state M) (s : nat) := t ≃(retr_sigCurrentState_sig; s) (halt q, index q).
Hint Resolve containsState_size_containsState : core.
Definition IsFinal_size := CasePair_size1 (default : bool) >> (S >> S) >> SetFinal_size@>Fin1.
Definition IsFinal_Rel : pRel sig^+ bool 2 := fun tin '(yout, tout) => forall (M : TM sigM 1) (q : state M) (s0 s1 : nat), let size := IsFinal_size in containsState_size tin[@Fin0] q s0 -> isVoid_size tin[@Fin1] s1 -> containsState_size tout[@Fin0] q s0 /\ isVoid_size tout[@Fin1] (size s1) /\ yout = halt q.
Definition IsFinal : pTM sig^+ bool 2 := CasePair (FinType(EqType bool)) (FinType(EqType sigNat)) ⇑ retr_sigCurrentState_sig @ [|Fin0; Fin1|];; If (CaseFin (FinType(EqType bool)) ⇑ retr_sigCurrentStateFinal_sig @ [|Fin1|]) (Return (SetFinal true @ [|Fin0; Fin1|]) true) (Return (SetFinal false @ [|Fin0; Fin1|]) false).
Definition IsFinal_steps (final : bool) := 2 + CasePair_steps (final) + CaseFin_steps + SetFinal_steps.
Definition IsFinal_T : tRel sig^+ 2 := fun tin k => exists (M : TM sigM 1) (q : state M), containsState tin[@Fin0] q /\ isVoid tin[@Fin1] /\ IsFinal_steps (halt q) <= k.
Definition graph_function (M : TM sigM 1) : option sigM * state M -> ((option sigM * move) * state M) := (fun '(s, q) => let (q', acts) := trans (q, [|s|]) in let (w, m) := acts[@Fin0] in ((w, m), q')).
Definition trans_map_keys (M : TM sigM 1) := fun (key : option sigM * (state M)) => let (s,q) := key in (s, (halt q, index q)).
Definition trans_map_values (M : TM sigM 1) := fun (value : (option sigM * move) * (state M)) => let (act, q') := value in (act, (halt q', index q')).
Definition graph_of_TM (M : TM sigM 1) : list ((option sigM * (bool * nat)) * ((option sigM * move) * (bool * nat))) := map (map_pair (trans_map_keys (M := M)) (trans_map_values (M := M))) (graph_of_fun (@graph_function M)).
Local Instance Encode_graph : codable sigGraph (list ((option sigM * (bool * nat)) * ((option sigM * move) * (bool * nat)))) := (Encode_list (Encode_pair (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat)) (Encode_pair (Encode_Finite _) (Encode_pair Encode_bool Encode_nat)))).
Definition containsTrans (t : tape sig^+) (M : TM sigM 1) := t ≃(retr_sigGraph_sig) (graph_of_TM M).
Definition containsTrans_size (t : tape sig^+) (M : TM sigM 1) (s : nat) := t ≃(retr_sigGraph_sig; s) (graph_of_TM M).
Hint Resolve containsTrans_size_containsTrans : core.
End Univ.

Lemma ReadCurrent'_Sem : ReadCurrent' ⊨c(ReadCurrent'_steps) ReadCurrent'_Rel.
Proof.
unfold ReadCurrent'_steps.
eapply RealiseIn_monotone.
{
unfold ReadCurrent'.
apply Switch_RealiseIn.
TM_Correct.
apply ReadCurrent_Sem.
intros c.
TM_Correct.
instantiate (1 := WriteValue_steps 1).
apply WriteValue_Sem.
}
{
cbn.
reflexivity.
}
{
intros tin ([], tout) H.
cbn.
intros tp s HCont HRight1.
TMSimp.
modpon H.
modpon H0.
subst.
split; auto.
contains_ext.
unfold WriteValue_size, ReadCurrent_size.
cbn.
lia.
}
