Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RequestVoteTermSanityInterface.
Require Import VerdiRaft.RequestVoteReplyTermSanityInterface.
Section RequestVoteReplyTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rvtsi : requestVote_term_sanity_interface}.
Instance rvrtsi : requestVoteReply_term_sanity_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply requestVoteReply_term_sanity_init.
-
apply requestVoteReply_term_sanity_client_request.
-
apply requestVoteReply_term_sanity_timeout.
-
apply requestVoteReply_term_sanity_append_entries.
-
apply requestVoteReply_term_sanity_append_entries_reply.
-
apply requestVoteReply_term_sanity_request_vote.
-
apply requestVoteReply_term_sanity_request_vote_reply.
-
apply requestVoteReply_term_sanity_do_leader.
-
apply requestVoteReply_term_sanity_do_generic_server.
-
apply requestVoteReply_term_sanity_state_same_packet_subset.
-
apply requestVoteReply_term_sanity_reboot.
End RequestVoteReplyTermSanity.

Lemma requestVoteReply_term_sanity_timeout : refined_raft_net_invariant_timeout requestVoteReply_term_sanity.
Proof using.
red.
unfold requestVoteReply_term_sanity.
intros.
simpl in *.
assert (In p (nwPackets net)) by (find_apply_hyp_hyp; intuition; exfalso; do_in_map; subst; simpl in *; unfold handleTimeout, tryToBecomeLeader in *; repeat break_match; find_inversion; simpl in *; intuition; do_in_map; subst; simpl in *; congruence).
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_apply_lem_hyp handleTimeout_log_term_type.
intuition; repeat find_rewrite; eauto.
