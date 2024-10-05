Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.AllEntriesLeaderLogsTermInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Section AllEntriesLeaderLogsTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Instance aellti : allEntries_leaderLogs_term_interface.
split.
exact allEntries_leaderLogs_term_invariant.
End AllEntriesLeaderLogsTerm.

Lemma allEntries_leaderLogs_term_client_request : refined_raft_net_invariant_client_request allEntries_leaderLogs_term.
Proof using.
unfold refined_raft_net_invariant_client_request, allEntries_leaderLogs_term.
simpl.
intros.
subst.
repeat find_higher_order_rewrite.
destruct_update.
-
simpl in *.
find_copy_apply_lem_hyp update_elections_data_client_request_allEntries.
intuition.
+
repeat find_rewrite.
find_apply_hyp_hyp.
intuition.
right.
break_exists_exists.
find_higher_order_rewrite.
destruct_update.
*
simpl in *.
rewrite update_elections_data_client_request_leaderLogs.
intuition.
*
intuition.
+
break_exists.
intuition.
find_rewrite.
simpl in *.
intuition.
*
find_inversion.
find_copy_apply_lem_hyp handleClientRequest_type.
intuition.
repeat find_rewrite.
intuition.
*
find_apply_hyp_hyp.
intuition.
right.
break_exists_exists.
find_higher_order_rewrite.
{
destruct_update.
*
simpl in *.
rewrite update_elections_data_client_request_leaderLogs.
intuition.
*
intuition.
}
-
find_apply_hyp_hyp.
intuition.
right.
break_exists_exists.
find_higher_order_rewrite.
{
destruct_update.
*
simpl in *.
rewrite update_elections_data_client_request_leaderLogs.
intuition.
*
intuition.
}
