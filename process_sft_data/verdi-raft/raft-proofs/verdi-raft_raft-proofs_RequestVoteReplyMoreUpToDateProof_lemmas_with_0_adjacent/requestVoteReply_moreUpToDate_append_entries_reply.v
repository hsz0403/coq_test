Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RequestVoteMaxIndexMaxTermInterface.
Require Import VerdiRaft.RequestVoteReplyTermSanityInterface.
Require Import VerdiRaft.VotedForMoreUpToDateInterface.
Require Import VerdiRaft.RequestVoteReplyMoreUpToDateInterface.
Section RequestVoteReplyMoreUpToDate.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rvmimti : requestVote_maxIndex_maxTerm_interface}.
Context {rvrtsi : requestVoteReply_term_sanity_interface}.
Context {vfmutdi : votedFor_moreUpToDate_interface}.
Instance rvrmutdi : requestVoteReply_moreUpToDate_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply requestVoteReply_moreUpToDate_init.
-
apply requestVoteReply_moreUpToDate_client_request.
-
apply requestVoteReply_moreUpToDate_timeout.
-
apply requestVoteReply_moreUpToDate_append_entries.
-
apply requestVoteReply_moreUpToDate_append_entries_reply.
-
apply requestVoteReply_moreUpToDate_request_vote.
-
apply requestVoteReply_moreUpToDate_request_vote_reply.
-
apply requestVoteReply_moreUpToDate_do_leader.
-
apply requestVoteReply_moreUpToDate_do_generic_server.
-
apply requestVoteReply_moreUpToDate_state_same_packet_subset.
-
apply requestVoteReply_moreUpToDate_reboot.
End RequestVoteReplyMoreUpToDate.

Lemma requestVoteReply_moreUpToDate_append_entries_reply : refined_raft_net_invariant_append_entries_reply requestVoteReply_moreUpToDate.
Proof using.
red.
unfold requestVoteReply_moreUpToDate.
intros.
simpl in *.
assert (In p0 (nwPackets net)) by (repeat find_rewrite; find_apply_lem_hyp handleAppendEntriesReply_packets; subst; simpl in *; find_apply_hyp_hyp; intuition; in_crush).
repeat find_rewrite.
find_copy_apply_lem_hyp handleAppendEntriesReply_votesReceived.
find_copy_apply_lem_hyp handleAppendEntriesReply_log_term_type.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; intuition; try congruence; repeat find_rewrite; eauto.
