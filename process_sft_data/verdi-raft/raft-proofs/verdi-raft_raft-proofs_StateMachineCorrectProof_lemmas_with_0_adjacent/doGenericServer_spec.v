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

Lemma doGenericServer_spec : forall (orig_base_params : BaseParams) (one_node_params : OneNodeParams orig_base_params) (raft_params : RaftParams orig_base_params) (h : name) (st : raft_data) (os : list raft_output) (st' : raft_data) (ps : list (name * msg)), doGenericServer h st = (os, st', ps) -> st' = st \/ log st' = log st /\ lastApplied st < lastApplied st' /\ lastApplied st' = commitIndex st /\ exists os' st'', applyEntries h st (rev (filter (fun x : entry => (lastApplied st <? eIndex x) && (eIndex x <=? commitIndex st)) (findGtIndex (log st) (lastApplied st)))) = (os', st'') /\ clientCache st' = clientCache st'' /\ forall c, getLastId st' c = getLastId st'' c.
Proof using.
intros.
unfold doGenericServer in *.
break_let.
break_if.
-
right.
do_bool.
find_inversion.
simpl in *.
intuition; eauto; use_applyEntries_spec; subst; simpl in *; auto.
-
left.
do_bool.
find_inversion.
match goal with | _ : applyEntries _ _ (rev ?l) = _ |- _ => enough (l = []) by (repeat find_rewrite; simpl in *; find_inversion; destruct r; simpl in *; auto) end.
erewrite filter_fun_ext_eq; eauto using filter_false.
intros.
simpl in *.
apply Bool.not_true_is_false.
intuition.
do_bool.
intuition.
do_bool.
use_applyEntries_spec.
subst.
simpl in *.
omega.
