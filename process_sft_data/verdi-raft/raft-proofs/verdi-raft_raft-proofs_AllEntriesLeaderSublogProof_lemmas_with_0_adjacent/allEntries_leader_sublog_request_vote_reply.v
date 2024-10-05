Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.AllEntriesCandidateEntriesInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Section AllEntriesLeaderSublog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {lsi : leader_sublog_interface}.
Context {olpti : one_leader_per_term_interface}.
Context {aecei : allEntries_candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Hint Resolve map_snd : core.
Instance aelsi : allEntries_leader_sublog_interface.
split.
intros.
apply refined_raft_net_invariant; auto.
-
apply allEntries_leader_sublog_init.
-
apply allEntries_leader_sublog_client_request.
-
apply allEntries_leader_sublog_timeout.
-
apply allEntries_leader_sublog_append_entries.
-
apply allEntries_leader_sublog_append_entries_reply.
-
apply allEntries_leader_sublog_request_vote.
-
apply allEntries_leader_sublog_request_vote_reply.
-
apply allEntries_leader_sublog_do_leader.
-
apply allEntries_leader_sublog_do_generic_server.
-
apply allEntries_leader_sublog_state_same_packet_subset.
-
apply allEntries_leader_sublog_reboot.
End AllEntriesLeaderSublog.

Lemma allEntries_leader_sublog_request_vote_reply : refined_raft_net_invariant_request_vote_reply allEntries_leader_sublog.
Proof using cci vci aecei.
red.
unfold allEntries_leader_sublog.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?v] => pose proof handleRequestVoteReply_spec h st h' t v (handleRequestVoteReply h st h' t v) end.
destruct_update; simpl in *; eauto; do_in_map; subst; destruct x; simpl in *; try find_rewrite_lem update_elections_data_requestVoteReply_allEntries; intuition; repeat find_rewrite; eauto; try congruence.
-
match goal with | _ : context [type ?st = Leader -> False] |- _ => destruct (serverType_eq_dec (type st) Leader) end; eauto.
+
match goal with | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ => pose proof handleRequestVoteReply_type h st h' t v (handleRequestVoteReply h st h' t v) end.
intuition; repeat find_rewrite; try congruence.
eauto.
+
intuition.
find_copy_apply_lem_hyp allEntries_candidateEntries_invariant; auto.
match goal with | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ => pose proof handleRequestVoteReply_RVR_spec h st h' t v (handleRequestVoteReply h st h' t v) end.
intuition; repeat find_rewrite; try congruence.
subst.
find_eapply_lem_hyp wonElection_candidateEntries_rvr; eauto using votes_correct_invariant, cronies_correct_invariant.
unfold ghost_data in *.
simpl in *.
unfold raft_refined_base_params, raft_refined_multi_params in *.
congruence.
-
match goal with | _ : context [type ?st = Leader -> False] |- _ => destruct (serverType_eq_dec (type st) Leader) end; eauto.
+
match goal with | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ => pose proof handleRequestVoteReply_type h st h' t v (handleRequestVoteReply h st h' t v) end.
intuition; repeat find_rewrite; try congruence.
eauto.
+
intuition.
find_copy_apply_lem_hyp allEntries_candidateEntries_invariant; auto.
match goal with | _ : context [handleRequestVoteReply ?h ?st ?h' ?t ?v] |- _ => pose proof handleRequestVoteReply_RVR_spec h st h' t v (handleRequestVoteReply h st h' t v) end.
intuition; repeat find_rewrite; try congruence.
subst.
find_eapply_lem_hyp wonElection_candidateEntries_rvr; eauto using votes_correct_invariant, cronies_correct_invariant.
unfold ghost_data in *.
simpl in *.
unfold raft_refined_base_params, raft_refined_multi_params in *.
congruence.
