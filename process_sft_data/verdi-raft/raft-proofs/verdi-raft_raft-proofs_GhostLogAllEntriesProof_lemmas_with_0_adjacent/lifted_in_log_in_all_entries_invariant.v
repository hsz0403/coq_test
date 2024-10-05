Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RaftMsgRefinementInterface.
Require Import VerdiRaft.InLogInAllEntriesInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.GhostLogAllEntriesInterface.
Section GhostLogAllEntriesProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rmri : raft_msg_refinement_interface}.
Context {iliaei : in_log_in_all_entries_interface}.
Definition lifted_in_log_in_all_entries (net : network) := forall h e, In e (log (snd (nwState net h))) -> exists t, In (t, e) (allEntries (fst (nwState net h))).
Instance glaei : ghost_log_allEntries_interface.
Proof.
split.
intros.
apply msg_refined_raft_net_invariant'; auto.
-
apply ghost_log_allEntries_init.
-
apply ghost_log_allEntries_client_request.
-
apply ghost_log_allEntries_timeout.
-
apply ghost_log_allEntries_append_entries.
-
apply ghost_log_allEntries_append_entries_reply.
-
apply ghost_log_allEntries_request_vote.
-
apply msg_refined_raft_net_invariant_request_vote_reply'_weak.
apply ghost_log_allEntries_request_vote_reply.
-
apply ghost_log_allEntries_do_leader.
-
apply ghost_log_allEntries_do_generic_server.
-
apply msg_refined_raft_net_invariant_subset'_weak.
apply ghost_log_allEntries_state_same_packet_subset.
-
apply msg_refined_raft_net_invariant_reboot'_weak.
apply ghost_log_allEntries_reboot.
End GhostLogAllEntriesProof.

Lemma lifted_in_log_in_all_entries_invariant : forall (net : @network _ raft_msg_refined_multi_params), msg_refined_raft_intermediate_reachable net -> lifted_in_log_in_all_entries net.
Proof using iliaei rmri.
intros.
unfold lifted_in_log_in_all_entries; intros.
find_eapply_lem_hyp msg_lift_prop; [|intros; eapply in_log_in_all_entries_invariant; eauto].
simpl in *.
unfold in_log_in_all_entries in *.
unfold mgv_deghost in *.
simpl in *.
repeat break_match; simpl in *; eauto.
