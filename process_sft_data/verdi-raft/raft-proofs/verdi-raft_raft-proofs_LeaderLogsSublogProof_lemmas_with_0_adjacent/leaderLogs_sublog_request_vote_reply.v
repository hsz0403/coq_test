Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.EveryEntryWasCreatedInterface.
Require Import VerdiRaft.LeaderLogsCandidateEntriesInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.LeaderLogsSublogInterface.
Section LeaderLogsSublog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lsi : leader_sublog_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {eewci : every_entry_was_created_interface}.
Context {llcei : leaderLogs_candidate_entries_interface}.
Context {cci : cronies_correct_interface}.
Context {vci : votes_correct_interface}.
Ltac start := repeat match goal with | [ H : _ |- _ ] => rewrite update_fun_comm with (f := fst) in H | [ H : _ |- _ ] => rewrite update_fun_comm with (f := snd) in H | [ H : _ |- _ ] => rewrite update_fun_comm with (f := leaderLogs) in H end; rewrite update_fun_comm with (f := snd); simpl in *; match goal with | [ H : context [ type ] |- _ ] => rewrite update_fun_comm in H; rewrite update_nop_ext' in H by auto end; match goal with | [ H : context [ currentTerm ] |- _ ] => rewrite update_fun_comm in H; rewrite update_nop_ext' in H by auto end.
Arguments dedup : simpl never.
Instance llsli : leaderLogs_sublog_interface.
Proof.
split.
exact leaderLogs_sublog_invariant.
End LeaderLogsSublog.

Theorem leaderLogs_sublog_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_sublog.
Proof using vci cci llcei lltsi lsi rri.
unfold refined_raft_net_invariant_request_vote_reply, leaderLogs_sublog.
simpl.
intuition.
repeat find_higher_order_rewrite.
find_copy_apply_lem_hyp handleRequestVoteReply_RVR_spec.
intuition.
-
subst.
repeat find_rewrite.
repeat update_destruct_max_simplify; eauto; find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition eauto; unfold raft_data in *; congruence.
-
repeat update_destruct_max_simplify; try congruence.
+
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition eauto.
subst_max.
repeat find_rewrite.
discriminate.
+
eauto.
-
repeat update_destruct_max_simplify.
+
repeat find_rewrite.
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
*
exfalso.
eauto using contradict_leaderLogs_term_sanity.
*
subst.
unfold raft_data in *.
repeat find_rewrite.
auto.
+
repeat find_rewrite.
exfalso.
eapply leaderLogs_candidate_entries_rvr; eauto; eauto using leaderLogs_candidate_entries_invariant, votes_correct_invariant, cronies_correct_invariant.
congruence.
+
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
*
eauto.
*
subst.
unfold raft_data in *.
repeat find_rewrite.
eapply lifted_leader_sublog_host; eauto.
+
eauto.
-
repeat update_destruct_max_simplify.
+
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
*
repeat find_rewrite.
eauto.
*
subst.
unfold raft_data in *.
repeat find_rewrite.
auto.
+
repeat find_rewrite.
eauto.
+
find_eapply_lem_hyp leaderLogs_update_elections_data_RVR; eauto; intuition.
*
repeat find_rewrite.
eauto.
*
subst.
unfold raft_data in *.
repeat find_rewrite.
discriminate.
+
eauto.
