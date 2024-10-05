Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.DecompositionWithPostState.
Require Import VerdiRaft.MaxIndexSanityInterface.
Require Import VerdiRaft.StateMachineSafetyInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.StateMachineCorrectInterface.
Section StateMachineCorrect.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Context {misi : max_index_sanity_interface}.
Context {smsi : state_machine_safety_interface}.
Context {lmi : log_matching_interface}.
Ltac get_invariant_pre inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => fail 2 end || copy_apply inv H end.
Ltac get_invariant_post inv := match goal with | H : raft_intermediate_reachable _ |- _=> match (type of H) with | context [mkNetwork] => copy_apply inv H end end.
Definition clientCache_to_ks (c : list (clientId * (nat * output))) := map (fun e => (fst e, fst (snd e))) c.
Fixpoint log_to_ks' (l : list entry) (ks : list (clientId * nat)) : list (clientId * nat) := match l with | e :: l' => if (assoc_default clientId_eq_dec ks (eClient e) 0) <=? eId e then log_to_ks' l' (assoc_set clientId_eq_dec ks (eClient e) (eId e)) else log_to_ks' l' ks | [] => ks end.
Definition log_to_ks l := log_to_ks' l [].
Definition client_cache_keys_correct net := forall h, a_equiv clientId_eq_dec (clientCache_to_ks (clientCache (nwState net h))) (log_to_ks' (rev (removeAfterIndex (log (nwState net h)) (lastApplied (nwState net h)))) []).
Fixpoint max_id_for_client_default (default : nat) (c : clientId) (l : list entry) : nat := match l with | [] => default | e :: l' => if clientId_eq_dec c (eClient e) then max_id_for_client_default (max default (eId e)) c l' else max_id_for_client_default default c l' end.
Ltac use_same_client_cache hyp := erewrite same_clientCache_same_getLastId in *; [|eapply hyp]; eauto.
Instance smci : state_machine_correct_interface.
Proof.
split.
exact state_machine_correct_invariant.
End StateMachineCorrect.

Lemma applyEntries_execute_log' : forall l h st os st', applyEntries h st l = (os, st') -> stateMachine st' = (snd (execute_log' (deduplicate_log' l (clientCache_to_ks (clientCache st))) (stateMachine st) [])).
Proof using.
induction l; intros; simpl in *; intuition.
-
find_inversion.
auto.
-
repeat break_let.
find_inversion.
repeat break_match; simpl in *.
+
break_let.
rewrite snd_execute_log'_nil.
find_apply_hyp_hyp.
do_bool.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply; [|eauto|idtac|]; eauto.
subst.
find_eapply_lem_hyp cacheApplyEntry_cache_apply; eauto.
erewrite clientCache_to_ks_assoc_set.
rewrite Heqp1.
eauto.
+
do_bool.
find_apply_hyp_hyp.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId.
break_exists.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_no_apply; eauto.
find_eapply_lem_hyp cacheApplyEntry_cache_no_apply; eauto.
repeat find_rewrite.
auto.
+
break_let.
rewrite snd_execute_log'_nil.
find_apply_hyp_hyp.
do_bool.
find_apply_lem_hyp clientCache_to_ks_assoc_getLastId_none.
break_exists.
find_copy_eapply_lem_hyp cacheApplyEntry_stateMachine_apply_none; eauto.
subst.
find_eapply_lem_hyp cacheApplyEntry_cache_apply_none; eauto.
erewrite clientCache_to_ks_assoc_set.
rewrite Heqp1.
eauto.
