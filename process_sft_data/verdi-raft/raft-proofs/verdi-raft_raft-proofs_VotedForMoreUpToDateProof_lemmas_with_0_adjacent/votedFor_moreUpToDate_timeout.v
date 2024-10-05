Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RequestVoteMaxIndexMaxTermInterface.
Require Import VerdiRaft.VotedForTermSanityInterface.
Require Import VerdiRaft.VotedForMoreUpToDateInterface.
Section VotedForMoreUpToDate.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rvmimti : requestVote_maxIndex_maxTerm_interface}.
Context {vftsi : votedFor_term_sanity_interface}.
Instance vfmutdi : votedFor_moreUpToDate_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply votedFor_moreUpToDate_init.
-
apply votedFor_moreUpToDate_client_request.
-
apply votedFor_moreUpToDate_timeout.
-
apply votedFor_moreUpToDate_append_entries.
-
apply votedFor_moreUpToDate_append_entries_reply.
-
apply votedFor_moreUpToDate_request_vote.
-
apply votedFor_moreUpToDate_request_vote_reply.
-
apply votedFor_moreUpToDate_do_leader.
-
apply votedFor_moreUpToDate_do_generic_server.
-
apply votedFor_moreUpToDate_state_same_packet_subset.
-
apply votedFor_moreUpToDate_reboot.
End VotedForMoreUpToDate.

Lemma votedFor_moreUpToDate_timeout : refined_raft_net_invariant_timeout votedFor_moreUpToDate.
Proof using vftsi.
red.
unfold votedFor_moreUpToDate.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
destruct_update_hyp; simpl in *; eauto.
-
find_copy_apply_lem_hyp handleTimeout_log_same.
find_copy_eapply_lem_hyp update_elections_data_timeout_votedFor; eauto.
intuition; repeat find_rewrite; eauto.
simpl.
eauto using moreUpToDate_refl.
-
find_copy_eapply_lem_hyp update_elections_data_timeout_votedFor; eauto.
intuition; [repeat find_rewrite; eauto|].
subst.
omega.
-
find_copy_apply_lem_hyp handleTimeout_log_same.
find_apply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived.
intuition; try congruence.
find_copy_apply_lem_hyp votedFor_term_sanity_invariant.
eapply_prop_hyp votedFor_term_sanity RaftState.votedFor; eauto.
unfold raft_data in *; simpl in *; unfold raft_data in *; simpl in *.
omega.
