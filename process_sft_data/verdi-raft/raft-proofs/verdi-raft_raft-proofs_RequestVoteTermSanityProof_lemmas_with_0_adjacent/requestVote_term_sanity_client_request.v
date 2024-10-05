Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RequestVoteTermSanityInterface.
Section RequestVoteTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Instance rvtsi : requestVote_term_sanity_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply requestVote_term_sanity_init.
-
apply requestVote_term_sanity_client_request.
-
apply requestVote_term_sanity_timeout.
-
apply requestVote_term_sanity_append_entries.
-
apply requestVote_term_sanity_append_entries_reply.
-
apply requestVote_term_sanity_request_vote.
-
apply requestVote_term_sanity_request_vote_reply.
-
apply requestVote_term_sanity_do_leader.
-
apply requestVote_term_sanity_do_generic_server.
-
apply requestVote_term_sanity_state_same_packet_subset.
-
apply requestVote_term_sanity_reboot.
End RequestVoteTermSanity.

Lemma requestVote_term_sanity_client_request : refined_raft_net_invariant_client_request requestVote_term_sanity.
Proof using.
red.
unfold requestVote_term_sanity.
intros.
simpl in *.
find_copy_apply_lem_hyp handleClientRequest_packets.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_apply_lem_hyp handleClientRequest_term_votedFor.
intuition; repeat find_rewrite; eauto.
