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

Lemma client_cache_correct_request_vote : raft_net_invariant_request_vote' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleRequestVote_clientCache.
erewrite handleRequestVote_same_log; eauto.
Admitted.

Lemma client_cache_correct_request_vote_reply : raft_net_invariant_request_vote_reply' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleRequestVoteReply_clientCache.
erewrite handleRequestVoteReply_log; eauto.
Admitted.

Lemma client_cache_correct_client_request : raft_net_invariant_client_request' client_cache_correct.
Proof using misi.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleClientRequest_clientCache.
Admitted.

Lemma client_cache_correct_timeout : raft_net_invariant_timeout' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache handleTimeout_clientCache.
erewrite handleTimeout_lastApplied; eauto.
Admitted.

Lemma client_cache_correct_do_leader : raft_net_invariant_do_leader' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
use_same_client_cache doLeader_clientCache.
erewrite doLeader_lastApplied; eauto.
Admitted.

Lemma client_cache_correct_reboot : raft_net_invariant_reboot' client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_higher_order_rewrite.
Admitted.

Lemma client_cache_correct_state_same_packet_subset : raft_net_invariant_state_same_packet_subset client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
subst.
find_reverse_higher_order_rewrite.
Admitted.

Lemma client_cache_correct_init : raft_net_invariant_init client_cache_correct.
Proof using.
red.
unfold client_cache_correct in *.
simpl in *.
intros.
unfold getLastId in *.
simpl in *.
Admitted.

Lemma client_cache_correct_invariant: forall (net : network), raft_intermediate_reachable net -> client_cache_correct net.
Proof using lmi smsi misi si.
intros.
apply raft_net_invariant'; auto.
-
apply client_cache_correct_init.
-
apply client_cache_correct_client_request.
-
apply client_cache_correct_timeout.
-
apply client_cache_correct_append_entries.
-
apply client_cache_correct_append_entries_reply.
-
apply client_cache_correct_request_vote.
-
apply client_cache_correct_request_vote_reply.
-
apply client_cache_correct_do_leader.
-
apply client_cache_correct_do_generic_server.
-
apply client_cache_correct_state_same_packet_subset.
-
Admitted.

Theorem state_machine_correct_invariant : forall net, raft_intermediate_reachable net -> state_machine_correct net.
Proof using lmi smsi misi si.
intros.
red.
intuition.
-
auto using state_machine_log_invariant.
-
auto using client_cache_correct_invariant.
-
Admitted.

Instance smci : state_machine_correct_interface.
Proof.
split.
exact state_machine_correct_invariant.
