From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import Hoare.Hoare HoareLegacy.
From Undecidability Require Import Univ.LookupAssociativeListTM.
From Undecidability Require Import Code.CaseFin Code.CaseList Code.CasePair.
From Undecidability Require Import Univ.LowLevel.
From Coq Require Import ArithRing Lia.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
Set Default Proof Using "Type".
Section Univ.
Variable (sigM : finType).
Notation sigGraph := (sigList (sigPair (sigPair (option sigM) sigState) (sigPair (option sigM * move) sigState))).
Variable (sig : finType).
Variable (retr_sigGraph_sig : Retract sigGraph sig).
Variable (retr_sigTape_sig : Retract sigM sig).
Local Existing Instance LowLevel.retr_sigCurrentStateNumber_sigGraph.
Local Existing Instance LowLevel.retr_sigCurrentStateNumber_sig.
Local Existing Instance LowLevel.retr_sigCurrentState_sigGraph.
Local Existing Instance LowLevel.retr_sigCurrentState_sig.
Local Existing Instance LowLevel.retr_sigCurrentStateFinal_sigGraph.
Local Existing Instance LowLevel.retr_sigCurrentStateFinal_sig.
Local Existing Instance LowLevel.retr_sigNextState_sigGraph.
Local Existing Instance LowLevel.retr_sigNextState_sig.
Local Existing Instance LowLevel.retr_sigCurrentSymbol_sigGraph.
Local Existing Instance LowLevel.retr_sigCurrentSymbol_sig.
Local Existing Instance LowLevel.retr_act_sigGraph.
Local Existing Instance LowLevel.retr_act_sig.
Local Existing Instance LowLevel.retr_key_sigGraph.
Local Existing Instance LowLevel.retr_key_sig.
Local Existing Instance LowLevel.retr_value_sigGraph.
Local Existing Instance LowLevel.retr_value_sig.
Local Existing Instance LowLevel.Encode_graph.
Local Existing Instance LowLevel.Encode_optSigM.
Local Existing Instance LowLevel.Encode_action.
Definition ContainsWorkingTape (tp : tape sigM) : RegSpec sig := Custom (fun t => containsWorkingTape _ t tp).
Definition DoAction'_size (a : option sigM * move) : Vector.t (nat->nat) 2 := [| (*0*) id; (*1*) DoAction_size a |].
Notation "'ContainsState' q" := (Contains (LowLevel.retr_sigCurrentState_sig _) (halt q, index q)) (at level 0).
Notation "'ContainsState_size' q s" := (Contains_size (LowLevel.retr_sigCurrentState_sig _) (halt q, index q) s) (at level 0).
Definition IsFinal_size' : Vector.t (nat->nat) 2 := [| (*0*) id; IsFinal_size |].
Definition ReadCurrent'_size : Vector.t (nat->nat) 2 := [| (*0*) id; ReadCurrent_size |].
Notation "'ContainsTrans' M" := (Contains (retr_sigGraph_sig) (graph_of_TM M)) (at level 0).
Notation "'ContainsTrans_size' M s" := (Contains_size (retr_sigGraph_sig) (graph_of_TM M) s) (at level 0).
Local Arguments graph_of_TM : simpl never.
Definition Univ_Step_size (M : TM sigM 1) (tp : tape sigM) (q : state M) : Vector.t (nat->nat) 6 := (* Note that the size function for tape 0 is semantically irrelevant because there is no size associated to this (working) tape *) if halt q then [|IsFinal_size|]@>>[|Fin3|] else let (q', act) := trans (q, [|current tp|]) in ([|IsFinal_size|]@>>[|Fin3|]) >>> ([|ReadCurrent_size|]@>>[|Fin3|]) >>> ([|Constr_pair_size (current tp)|]@>>[|Fin2|]) >>> ([|Reset_size (current tp)|] @>> [|Fin3|]) >>> (Lookup_size (graph_of_TM M) (current tp, (halt q, index q)) @>> [|Fin1; Fin2; Fin3; Fin4; Fin5|]) >>> ([|CasePair_size0 act[@Fin0]; CasePair_size1 act[@Fin0]|] @>> [|Fin2; Fin3|]) >>> ([|DoAction_size act[@Fin0]|] @>> [|Fin3|]).
Definition Univ_Step_steps_ConstrPair (tp : tape sigM) := Constr_pair_steps (current tp).
Definition Univ_Step_steps_ResetSymbol (tp : tape sigM) := Reset_steps (current tp).
Definition Univ_Step_steps_Lookup (M : TM sigM 1) (q : state M) (tp : tape sigM) := Lookup_steps (current tp, (halt q, index q)) (graph_of_TM M).
Definition Univ_Step_steps_CasePair (a : option sigM * move) := CasePair_steps a.
Definition Univ_Step_steps_Translate (M : TM sigM 1) (q' : state M) := Translate_steps (halt q', index q').
Definition Univ_Step_steps_IsFinal (M : TM sigM 1) (q : state M) (tp : tape sigM) := if halt q then 0 else let (q', acts) := trans (q, [|current tp|]) in 6 + ReadCurrent'_steps + Univ_Step_steps_ConstrPair tp + Univ_Step_steps_ResetSymbol tp + Univ_Step_steps_Lookup q tp + Univ_Step_steps_CasePair acts[@Fin0] + DoAction'_steps + Univ_Step_steps_Translate q'.
Definition Univ_Step_steps (M : TM sigM 1) (q : state M) (tp : tape sigM) : nat := 1 + IsFinal_steps (halt q) + Univ_Step_steps_IsFinal q tp.
Definition Univ_Step : pTM sig^+ (option unit) 6 := If (IsFinal _ @ [|Fin2; Fin3|]) (Return Nop (Some tt)) (Return (ReadCurrent' _ _ @ [|Fin0; Fin3|];; Constr_pair (FinType(EqType (option sigM))) (FinType(EqType sigState)) ⇑ LowLevel.retr_key_sig _ @ [|Fin3; Fin2|];; Reset _ @ [|Fin3|];; Lookup _ _ ⇑ retr_sigGraph_sig @ [|Fin1; Fin2; Fin3; Fin4; Fin5|];; CasePair (FinType(EqType(option sigM * move))) (FinType(EqType(sigState))) ⇑ LowLevel.retr_value_sig _ @ [|Fin2; Fin3|];; DoAction' _ _ @ [|Fin0; Fin3|];; Translate (LowLevel.retr_sigNextState_sig _) (LowLevel.retr_sigCurrentState_sig _) @ [|Fin2|]) None).
Definition Univ := While Univ_Step.
Fixpoint Univ_size (M : TM sigM 1) (tp : tape sigM) (q : state M) (k : nat) {struct k} : Vector.t (nat->nat) 6 := match k with | 0 => Univ_Step_size tp q | S k' => if halt q then Univ_Step_size tp q else let (q', tp') := step (mk_mconfig q [|tp|]) in Univ_Step_size tp q >>> Univ_size tp'[@Fin0] q' k' end.
Fixpoint Univ_steps (M : TM sigM 1) (q : state M) (tp : tape sigM) (k : nat) : nat := match k with | 0 => Univ_Step_steps q tp | S k' => if halt q then Univ_Step_steps q tp else let (q', tp') := step (mk_mconfig q [|tp|]) in 1 + Univ_Step_steps q tp + Univ_steps q' tp'[@Fin0] k' end.
Section LegacyLemmas.
Definition Univ_Rel : pRel sig^+ unit 6 := fun tin '(_, tout) => forall (M : TM sigM 1) (tp : tape sigM) (q : state M) (s1 s2 : nat) (sr : Vector.t nat 3), containsWorkingTape _ tin[@Fin0] tp -> containsTrans_size _ tin[@Fin1] M s1 -> containsState_size _ tin[@Fin2] q s2 -> (forall (i : Fin.t 3), isVoid_size tin[@FinR 3 i] sr[@i]) -> exists k (oconf : mconfig sigM (state M) 1), let size := Univ_size tp q k in loopM (mk_mconfig q [|tp|]) k = Some oconf /\ containsWorkingTape _ tout[@Fin0] (ctapes oconf)[@Fin0] /\ containsTrans_size _ tout[@Fin1] M (size@>Fin1 s1) /\ containsState_size _ tout[@Fin2] (cstate oconf) (size@>Fin2 s2) /\ (forall (i : Fin.t 3), isVoid_size tout[@FinR 3 i] (size@>(FinR 3 i) sr[@i])).
Definition Univ_T : tRel sig^+ 6 := fun tin k => exists (M : TM sigM 1) (tp : tape sigM) (q : state M) (k' : nat) (q' : state M) (tp' : tape sigM), containsWorkingTape _ tin[@Fin0] tp /\ containsTrans _ tin[@Fin1] M /\ containsState _ tin[@Fin2] q /\ (forall (i : Fin.t 3), isVoid tin[@FinR 3 i]) /\ loopM (mk_mconfig q [|tp|]) k' = Some (mk_mconfig q' [|tp'|]) /\ Univ_steps q tp k' <= k.
End LegacyLemmas.
End Univ.

Lemma Univ_Step_SpecT_space (M : TM sigM 1) (tp : tape sigM) (q : state M) ss : TripleT (≃≃([],withSpace ([|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|]) ss)) (Univ_Step_steps q tp) Univ_Step (fun yout => ≃≃([yout = if halt q then Some tt else None], withSpace (if halt q then [|ContainsWorkingTape tp; ContainsTrans M; ContainsState q; Void; Void; Void|] else let (q', tp') := step (mk_mconfig q [|tp|]) in let tp' := tp'[@Fin0] in [|ContainsWorkingTape tp'; ContainsTrans M; ContainsState q'; Void; Void; Void|]) (appSize (Univ_Step_size tp q) ss))).
Proof.
cbn.
destruct step eqn:HStep.
cbn.
destruct (trans (q, [|current tp|])) as (q'&a) eqn:Etrans.
unfold step, current_chars in HStep.
cbn in *.
rewrite Etrans in HStep.
symmetry in HStep.
inv HStep.
eapply If_SpecT with (k2 := Univ_Step_steps_IsFinal q tp) (k3 := Univ_Step_steps_IsFinal q tp).
+
hsteps_cbn.
cbn.
eapply ConsequenceT_pre.
*
apply IsFinal_SpecT_space with (q := q).
*
reflexivity.
*
reflexivity.
+
cbn.
hintros Ehalt.
hsteps_cbn.
apply Nop_SpecT_con.
unfold Univ_Step_size.
rewrite <- Ehalt.
tspec_ext.
+
cbn.
hintros Ehalt.
rewrite <- Ehalt.
hsteps_cbn; cbn.
6-8:reflexivity.
*
apply ReadCurrent'_SpecT_space.
*
cbn.
intros.
tspec_ext.
*
cbn.
refine (Lookup_SpecT_space _ _ _ _ _).
2:apply transition_graph_injective.
all:shelve.
*
cbn.
tspec_ext.
*
cbn.
hintros ? ->.
rewrite Ehalt.
erewrite lookup_graph with (tp := tp).
rewrite Etrans; cbn.
hstep; cbn.
3:reflexivity.
hstep; cbn.
hstep; cbn.
hstep; cbn.
instantiate (1 := (a[@Fin0], (halt q', index q'))).
cbn.
tspec_ext.
cbn.
intros _.
hstep; cbn.
3:reflexivity.
hstep; cbn.
eapply ConsequenceT_pre.
3:reflexivity.
--
apply DoAction'_SpecT_space with (a := a[@Fin0]).
--
instantiate (1 := [| _;_|]).
tspec_ext.
eassumption.
--
cbn.
intros _.
hstep; cbn.
eapply ConsequenceT_pre.
3:reflexivity.
++
refine (@Translate_SpecT_size _ _ _ _ _ _ _ _).
all:shelve.
++
instantiate (1 := [| _|]).
tspec_ext.
*
unfold Univ_Step_steps_IsFinal.
rewrite <- Ehalt.
rewrite Etrans.
cbn.
unfold Univ_Step_steps_ConstrPair, Univ_Step_steps_CasePair, Univ_Step_steps_Lookup, Univ_Step_steps_ResetSymbol, Univ_Step_steps_Translate.
rewrite <- !Ehalt.
ring_simplify.
set (Lookup_steps _ _).
nia.
*
unfold_abbrev.
cbn.
rewrite <- Ehalt.
cbn.
unfold Univ_Step_size.
rewrite <- Ehalt,Etrans.
tspec_ext.
cbn.
specialize (H Fin0).
cbn in *.
simpl_tape.
auto.
+
cbn.
intros ? ? ? _ _.
destruct yout; auto.
