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

Lemma allEntries_leaderLogs_term_request_vote_reply : refined_raft_net_invariant_request_vote_reply allEntries_leaderLogs_term.
Proof using.
unfold refined_raft_net_invariant_request_vote_reply, allEntries_leaderLogs_term.
simpl.
intros.
repeat find_higher_order_rewrite.
destruct_update.
-
simpl in *.
find_rewrite_lem update_elections_data_requestVoteReply_allEntries.
find_apply_hyp_hyp.
intuition.
right.
break_exists_exists.
find_higher_order_rewrite.
destruct_update.
+
simpl.
intuition.
apply update_elections_data_requestVoteReply_old.
auto.
+
auto.
-
find_apply_hyp_hyp.
intuition.
right.
break_exists_exists.
find_higher_order_rewrite.
destruct_update.
+
simpl.
intuition.
apply update_elections_data_requestVoteReply_old.
auto.
+
auto.
