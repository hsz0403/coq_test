Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsInterface.
Require Import VerdiRaft.AppendEntriesRequestsCameFromLeadersInterface.
Section AppendEntriesRequestsCameFromLeaders.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lhlli : leaders_have_leaderLogs_interface}.
Context {rri : raft_refinement_interface}.
Ltac start := red; unfold append_entries_came_from_leaders; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct_hyp; subst; rewrite_update; eauto; simpl in *.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Ltac contra := (exfalso; intuition; find_false; repeat eexists; eauto).
Instance aercfli : append_entries_came_from_leaders_interface.
split.
exact append_entries_came_from_leaders_invariant.
End AppendEntriesRequestsCameFromLeaders.

Lemma append_entries_came_from_leaders_appendEntries : refined_raft_net_invariant_append_entries append_entries_came_from_leaders.
Proof using.
red.
unfold append_entries_came_from_leaders.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
prove_in.
find_apply_hyp_hyp.
break_exists.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
rewrite update_elections_data_appendEntries_leaderLogs.
repeat find_rewrite.
eauto.
-
subst.
simpl in *.
subst.
find_apply_lem_hyp handleAppendEntries_not_append_entries.
exfalso.
intuition.
find_false.
repeat eexists; eauto.
