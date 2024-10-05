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

Lemma requestVoteReply_moreUpToDate_request_vote : refined_raft_net_invariant_request_vote requestVoteReply_moreUpToDate.
Proof using vfmutdi rvmimti.
red.
unfold requestVoteReply_moreUpToDate.
intros.
simpl in *.
find_copy_apply_lem_hyp handleRequestVote_votesReceived.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
-
find_copy_apply_lem_hyp handleRequestVote_log_term_type; intuition; try congruence.
repeat find_rewrite.
find_apply_hyp_hyp.
intuition.
+
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
repeat find_rewrite.
eapply_prop_hyp pBody pBody; eauto.
break_exists_exists.
intuition.
eauto using update_elections_data_request_vote_votesWithLog_old.
+
remember (pSrc p0) as h.
subst_max.
simpl in *.
subst_max.
find_copy_apply_lem_hyp handleRequestVote_reply_true.
find_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto; intuition; eauto; repeat find_rewrite.
*
find_eapply_lem_hyp votedFor_moreUpToDate_invariant; eauto.
repeat conclude_using eauto.
break_exists_exists; intuition; eauto using update_elections_data_request_vote_votesWithLog_old.
*
find_apply_lem_hyp requestVote_maxIndex_maxTerm_invariant.
eapply_prop_hyp requestVote_maxIndex_maxTerm pBody; eauto.
concludes.
intuition; subst.
eexists; intuition; eauto.
-
find_copy_apply_lem_hyp handleRequestVote_log_term_type; intuition; try congruence.
repeat find_rewrite.
find_apply_hyp_hyp.
intuition.
+
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
repeat find_rewrite.
eapply_prop_hyp pBody pBody; eauto.
+
remember (pDst p0) as h.
subst_max.
simpl in *.
subst_max.
find_copy_apply_lem_hyp handleRequestVote_reply_true.
intuition.
-
find_apply_hyp_hyp; intuition.
+
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
repeat find_rewrite.
eapply_prop_hyp pBody pBody; eauto.
break_exists_exists.
intuition.
eauto using update_elections_data_request_vote_votesWithLog_old.
+
remember (pSrc p0) as h.
subst.
simpl in *.
subst.
find_copy_apply_lem_hyp handleRequestVote_reply_true.
intuition.
find_eapply_lem_hyp update_elections_data_request_vote_votedFor; eauto.
intuition; repeat find_rewrite; eauto.
*
find_copy_apply_lem_hyp votedFor_moreUpToDate_invariant.
eapply_prop_hyp votedFor_moreUpToDate RaftState.votedFor; eauto.
concludes.
break_exists_exists; intuition; eauto using update_elections_data_request_vote_votesWithLog_old.
*
find_apply_lem_hyp requestVote_maxIndex_maxTerm_invariant.
eapply_prop_hyp requestVote_maxIndex_maxTerm pBody; eauto.
concludes.
intuition; subst.
eexists; intuition; eauto.
-
find_apply_hyp_hyp.
intuition.
+
assert (In p0 (nwPackets net)) by (repeat find_rewrite; in_crush).
repeat find_rewrite.
eapply_prop_hyp pBody pBody; eauto.
+
subst.
simpl in *.
subst.
simpl in *.
find_copy_apply_lem_hyp handleRequestVote_reply_true.
intuition.
