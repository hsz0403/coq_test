Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.AllEntriesIndicesGt0Interface.
Section AllEntriesIndicesGt0.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Instance aeigt0 : allEntries_indices_gt_0_interface.
Proof.
constructor.
exact allEntries_indices_gt_0_invariant.
End AllEntriesIndicesGt0.

Lemma allEntries_indices_gt_0_invariant : forall net, refined_raft_intermediate_reachable net -> allEntries_indices_gt_0 net.
Proof using taifoli rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply allEntries_indices_gt_0_init.
-
apply allEntries_indices_gt_0_client_request.
-
apply allEntries_indices_gt_0_timeout.
-
apply allEntries_indices_gt_0_append_entries.
-
apply allEntries_indices_gt_0_append_entries_reply.
-
apply allEntries_indices_gt_0_request_vote.
-
apply allEntries_indices_gt_0_request_vote_reply.
-
apply allEntries_indices_gt_0_do_leader.
-
apply allEntries_indices_gt_0_do_generic_server.
-
apply allEntries_indices_gt_0_state_same_packet_subset.
-
apply allEntries_indices_gt_0_reboot.
