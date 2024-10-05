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

Lemma allEntries_leaderLogs_term_append_entries : refined_raft_net_invariant_append_entries allEntries_leaderLogs_term.
Proof using aerlli.
red.
unfold allEntries_leaderLogs_term.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
destruct_update; simpl in *; [|find_apply_hyp_hyp; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto].
find_apply_lem_hyp update_elections_data_appendEntries_allEntries_term.
intuition; [find_apply_hyp_hyp; intuition; right; break_exists_exists; intuition; find_higher_order_rewrite; destruct_update; simpl in *; eauto; rewrite update_elections_data_appendEntries_leaderLogs; eauto|].
subst.
match goal with | H : context [pBody] |- _ => eapply append_entries_leaderLogs_invariant in H; eauto end.
break_exists.
break_and.
subst.
do_in_app.
case H7; intros; try find_apply_hyp_hyp; auto.
right.
find_eapply_lem_hyp Prefix_In; eauto.
repeat eexists; eauto.
find_higher_order_rewrite; destruct_update; simpl in *; eauto; rewrite update_elections_data_appendEntries_leaderLogs; subst; eauto.
