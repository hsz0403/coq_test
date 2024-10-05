Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Section AppendEntriesRequestLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {nisi : nextIndex_safety_interface}.
Ltac start := red; unfold append_entries_leaderLogs; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance aerlli : append_entries_leaderLogs_interface.
split.
exact append_entries_leaderLogs_invariant.
End AppendEntriesRequestLeaderLogs.

Lemma append_entries_leaderLogs_appendEntriesReply : refined_raft_net_invariant_append_entries_reply append_entries_leaderLogs.
Proof using.
red.
unfold append_entries_leaderLogs.
intros.
subst.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
-
prove_in.
eapply_prop_hyp In In; break_exists.
intuition; eauto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
+
repeat eexists; intuition eauto.
repeat find_higher_order_rewrite.
update_destruct; subst_max; rewrite_update; simpl in *; eauto; subst; auto.
+
eauto.
-
do_in_map.
subst.
simpl in *.
unfold handleAppendEntriesReply in *.
repeat break_match; find_inversion; simpl in *; intuition.
