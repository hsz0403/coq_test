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

Lemma requestVoteReply_term_sanity_do_generic_server : refined_raft_net_invariant_do_generic_server requestVoteReply_term_sanity.
Proof using.
red.
unfold requestVoteReply_term_sanity.
intros.
simpl in *.
find_copy_apply_lem_hyp doGenericServer_packets.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto; find_apply_lem_hyp doGenericServer_log_type_term_votesReceived; intuition; repeat find_rewrite; eauto.
