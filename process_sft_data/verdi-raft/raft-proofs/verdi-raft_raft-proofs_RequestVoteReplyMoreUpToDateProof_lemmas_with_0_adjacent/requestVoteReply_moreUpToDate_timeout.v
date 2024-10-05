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

Lemma requestVoteReply_moreUpToDate_timeout : refined_raft_net_invariant_timeout requestVoteReply_moreUpToDate.
Proof using rvrtsi.
red.
unfold requestVoteReply_moreUpToDate.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
-
find_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
intuition; try congruence.
repeat find_rewrite.
simpl in *.
intuition.
subst.
exists (log d).
intuition.
auto using moreUpToDate_refl.
-
find_copy_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
intuition; try congruence.
repeat find_rewrite.
simpl in *.
find_eapply_lem_hyp requestVoteReply_term_sanity_invariant; eauto; unfold raft_data in *; simpl in *; unfold raft_data in *; simpl in *; try omega; [idtac].
find_apply_hyp_hyp.
intuition.
exfalso.
do_in_map.
remember (pDst p) as h.
subst p.
simpl in *.
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; find_inversion; simpl in *; intuition.
-
find_apply_hyp_hyp.
intuition.
+
eapply_prop_hyp pBody pBody; eauto.
break_exists_exists; intuition; eauto using update_elections_data_timeout_votesWithLog_old.
+
exfalso.
do_in_map.
remember (pSrc p).
subst p.
simpl in *.
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; find_inversion; simpl in *; intuition; do_in_map; subst; simpl in *; congruence.
-
find_apply_hyp_hyp.
intuition.
+
eapply_prop_hyp pBody pBody; eauto.
+
exfalso.
do_in_map.
remember (pSrc p).
subst p.
simpl in *.
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; find_inversion; simpl in *; intuition; do_in_map; subst; simpl in *; congruence.
