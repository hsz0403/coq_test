Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RequestVoteReplyMoreUpToDateInterface.
Require Import VerdiRaft.VotesReceivedMoreUpToDateInterface.
Section VotesReceivedMoreUpToDate.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rvrmutdi : requestVoteReply_moreUpToDate_interface}.
Instance vrmutdi : votesReceived_moreUpToDate_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply votesReceived_moreUpToDate_init.
-
apply votesReceived_moreUpToDate_client_request.
-
apply votesReceived_moreUpToDate_timeout.
-
apply votesReceived_moreUpToDate_append_entries.
-
apply votesReceived_moreUpToDate_append_entries_reply.
-
apply votesReceived_moreUpToDate_request_vote.
-
apply votesReceived_moreUpToDate_request_vote_reply.
-
apply votesReceived_moreUpToDate_do_leader.
-
apply votesReceived_moreUpToDate_do_generic_server.
-
apply votesReceived_moreUpToDate_state_same_packet_subset.
-
apply votesReceived_moreUpToDate_reboot.
End VotesReceivedMoreUpToDate.

Lemma votesReceived_moreUpToDate_timeout : refined_raft_net_invariant_timeout votesReceived_moreUpToDate.
Proof using.
red.
unfold votesReceived_moreUpToDate.
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
find_eapply_lem_hyp update_elections_data_timeout_votesWithLog_votesReceived; eauto.
intuition; try congruence.
repeat find_rewrite.
simpl in *.
intuition.
-
eapply_prop_hyp Candidate Candidate; eauto.
break_exists_exists.
intuition.
apply update_elections_data_timeout_votesWithLog_old.
try rewrite <- plus_n_O in *.
auto.
