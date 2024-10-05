Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LeaderLogsLogPropertiesInterface.
Section LogsLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {lllmi : leaderLogs_entries_match_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {nisi : nextIndex_safety_interface}.
Context {si : sorted_interface}.
Context {lpholli : log_properties_hold_on_leader_logs_interface}.
Definition weak_sanity pli ll ll' := pli = 0 -> (exists e, eIndex e = 0 /\ In e ll) \/ ll = ll'.
Definition logs_leaderLogs_nw_weak net := forall p t n pli plt es ci e, In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In e es -> exists leader ll es' ll', In (eTerm e, ll) (leaderLogs (fst (nwState net leader))) /\ Prefix ll' ll /\ removeAfterIndex es (eIndex e) = es' ++ ll' /\ (forall e', In e' es' -> eTerm e' = eTerm e) /\ weak_sanity pli ll ll'.
Definition logs_leaderLogs_inductive net := logs_leaderLogs net /\ logs_leaderLogs_nw net.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance llli : logs_leaderLogs_interface.
Proof.
split; eauto using logs_leaderLogs_invariant, logs_leaderLogs_nw_invariant.
End LogsLeaderLogs.

Lemma logs_leaderLogs_inductive_appendEntries : refined_raft_net_invariant_append_entries logs_leaderLogs_inductive.
Proof using lpholli si lllmi llci rlmli llsi rri.
red.
unfold logs_leaderLogs_inductive.
intros.
subst.
simpl in *.
intuition.
-
unfold logs_leaderLogs in *.
intros.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
+
simpl in *.
find_apply_lem_hyp handleAppendEntries_log.
intuition; repeat find_rewrite; eauto.
*
find_apply_hyp_hyp.
break_exists_exists; intuition.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
simpl in *.
rewrite update_elections_data_appendEntries_leaderLogs.
auto.
*
{
subst.
find_apply_lem_hyp logs_leaderLogs_nw_weaken.
unfold logs_leaderLogs_nw_weak in *.
copy_eapply_prop_hyp pBody pBody; eauto.
break_exists_exists.
break_exists.
intuition.
-
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl.
rewrite update_elections_data_appendEntries_leaderLogs.
auto.
-
repeat find_rewrite.
f_equal.
find_copy_apply_lem_hyp leaderLogs_sorted_invariant; eauto.
eapply sorted_Prefix_in_eq; eauto.
intros.
eapply prefix_contiguous with (i := 0); eauto.
+
unfold weak_sanity in *.
concludes.
intuition; subst; simpl in *; intuition.
break_exists.
intuition.
find_eapply_lem_hyp leaderLogs_contiguous_invariant; eauto.
omega.
+
eapply leaderLogs_contiguous_invariant; eauto.
+
assert (sorted (log d)) by (eapply entries_sorted_nw_invariant; eauto).
eapply contiguous_app with (l1 := x1).
*
repeat find_reverse_rewrite.
apply removeAfterIndex_sorted.
auto.
*
repeat find_reverse_rewrite.
eapply removeAfterIndex_contiguous; eauto.
eapply entries_contiguous_nw_invariant; eauto.
}
*
{
break_exists.
intuition.
subst.
do_in_app.
intuition.
-
unfold logs_leaderLogs_nw in *.
prove_in.
copy_eapply_prop_hyp In In; eauto.
match goal with | H:exists _, _ |- _ => destruct H as [leader] end.
break_exists; intuition.
+
assert (x2 = []).
{
destruct x2; intuition.
exfalso.
simpl in *.
break_match; intuition.
simpl in *.
subst.
find_copy_apply_lem_hyp entries_contiguous_nw_invariant.
eapply_prop_hyp entries_contiguous_nw pBody; eauto.
unfold contiguous_range_exact_lo in *.
intuition.
match goal with | _ : removeAfterIndex _ ?index = _ ++ ?e :: _ |- _ => assert (In e es) by (apply removeAfterIndex_in with (i := index); repeat find_rewrite; intuition) end.
eapply_prop_hyp In In.
omega.
}
subst.
rewrite app_nil_r in *.
match goal with | H : forall _ _, In _ _ -> _ |- _ => specialize (H0 (pDst p) x) end.
intuition.
break_exists.
intuition.
match goal with | _ : In (_, ?ll) (leaderLogs (_ (_ _ ?h))), _ : removeAfterIndex _ _ = ?es' ++ ?ll |- _ => exists h, ll, (removeAfterIndex es (eIndex e) ++ es') end.
intuition.
*
repeat find_rewrite.
match goal with | H : forall _, st' _ = _ |- _ => rewrite H end.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
rewrite update_elections_data_appendEntries_leaderLogs.
auto.
*
rewrite removeAfterIndex_in_app; auto.
rewrite app_ass.
repeat find_rewrite.
auto.
*
repeat find_rewrite.
do_in_app.
intuition; eauto.
+
break_exists; intuition; match goal with | [ _ : In (_, ?ll) (leaderLogs (_ (_ _ ?leader))), _ : removeAfterIndex _ _ = ?es' ++ _ |- _ ] => exists leader, ll, es' end; intuition.
*
repeat find_rewrite.
match goal with | H : forall _, st' _ = _ |- _ => rewrite H end.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
rewrite update_elections_data_appendEntries_leaderLogs.
auto.
*
rewrite removeAfterIndex_in_app; auto.
repeat find_rewrite.
rewrite app_ass.
find_copy_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
f_equal.
eapply thing; eauto using lift_logs_sorted; [eauto using leaderLogs_contiguous|eapply leaderLogs_entries_match_invariant; eauto|].
assert (sorted es) by (eapply entries_sorted_nw_invariant; eauto).
find_copy_apply_lem_hyp entries_contiguous_nw_invariant.
unfold entries_contiguous_nw in *.
copy_eapply_prop_hyp contiguous_range_exact_lo pBody; eauto.
find_eapply_lem_hyp removeAfterIndex_contiguous; eauto.
match goal with | H : removeAfterIndex _ _ = _ |- _ => find_erewrite_lem H end.
eapply contiguous_app; eauto.
repeat find_reverse_rewrite.
eauto using removeAfterIndex_sorted.
*
repeat find_rewrite.
match goal with | H : forall _, st' _ = _ |- _ => rewrite H end.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
rewrite update_elections_data_appendEntries_leaderLogs.
auto.
*
rewrite removeAfterIndex_in_app; auto.
repeat find_rewrite.
rewrite app_ass.
f_equal.
assert (x2 = []).
{
destruct x2; intuition.
exfalso.
simpl in *.
break_match; intuition.
simpl in *.
subst.
find_copy_apply_lem_hyp entries_contiguous_nw_invariant.
eapply_prop_hyp entries_contiguous_nw pBody; eauto.
unfold contiguous_range_exact_lo in *.
break_and.
match goal with | _ : removeAfterIndex _ ?index = _ ++ ?e :: _ |- _ => assert (In e es) by (apply removeAfterIndex_in with (i := index); repeat find_rewrite; intuition) end.
clear H0 H7.
eapply_prop_hyp In In.
omega.
}
subst.
simpl.
find_copy_eapply_lem_hyp leaderLogs_sorted_invariant; eauto.
match goal with | |- _ = ?ll => rewrite removeAfterIndex_maxIndex_sorted with (l := ll) at 2 end; eauto.
eapply removeAfterIndex_same_sufficient; eauto using lift_logs_sorted; intros; match goal with | _ : eIndex ?e = maxIndex _, _ : In ?e (log _), _ : eIndex ?e' = maxIndex _ |- In ?e'' _ => assert (eIndex e = eIndex e') as Heq by (repeat find_rewrite; auto); assert (eIndex e'' <= eIndex e) by omega; eapply leaderLogs_entries_match_invariant in Heq; eauto; repeat conclude Heq ltac:(eauto; intuition) end; intuition.
-
find_copy_apply_lem_hyp removeAfterIndex_in.
find_copy_apply_lem_hyp removeAfterIndex_In_le; eauto using lift_logs_sorted.
find_apply_hyp_hyp.
break_exists_exists; intuition.
+
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
simpl in *.
rewrite update_elections_data_appendEntries_leaderLogs.
auto.
+
rewrite removeAfterIndex_in_app_l'; eauto; [rewrite <- removeAfterIndex_le; auto|].
intros.
eapply gt_le_trans; [|eauto].
eapply entries_contiguous_nw_invariant; eauto.
}
+
find_apply_hyp_hyp.
break_exists_exists; intuition.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
simpl in *.
rewrite update_elections_data_appendEntries_leaderLogs.
auto.
-
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
prove_in.
copy_eapply_prop_hyp In In; eauto.
break_exists_exists; intuition; repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_appendEntries_leaderLogs; auto.
+
exfalso.
subst.
simpl in *.
unfold handleAppendEntries in *; repeat break_match; find_inversion; congruence.
