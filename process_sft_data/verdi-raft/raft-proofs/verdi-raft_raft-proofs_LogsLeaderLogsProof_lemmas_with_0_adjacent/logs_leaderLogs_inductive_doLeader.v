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

Lemma logs_leaderLogs_inductive_doLeader : refined_raft_net_invariant_do_leader logs_leaderLogs_inductive.
Proof using si nisi rlmli llsi rri.
red.
unfold logs_leaderLogs_inductive.
intros.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
intuition.
-
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_apply_lem_hyp doLeader_log.
find_higher_order_rewrite.
simpl in *.
update_destruct; subst; rewrite_update; simpl in *; repeat find_rewrite; find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
-
unfold logs_leaderLogs_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
break_or_hyp.
+
unfold logs_leaderLogs_nw in *.
eapply_prop_hyp pBody pBody; eauto.
break_exists_exists; intuition; subst; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
+
{
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp doLeader_spec; eauto.
intuition.
-
subst.
unfold logs_leaderLogs in *.
find_apply_lem_hyp findGtIndex_necessary.
intuition.
eapply_prop_hyp In In.
break_exists_exists.
intuition.
match goal with | _ : In (_, ?ll) _ |- _ => exists ll end.
intuition; eauto using Prefix_refl; [find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto|].
rewrite sorted_findGtIndex_0; eauto using lift_logs_sorted.
intros.
eapply entries_gt_0_invariant; eauto.
-
break_exists.
break_and.
subst.
unfold logs_leaderLogs in *.
find_apply_lem_hyp findGtIndex_necessary.
break_and.
find_apply_hyp_hyp.
match goal with | H : exists _ _ _, _ |- _ => destruct H as [leader]; destruct H as [ll]; destruct H as [es] end.
break_and.
destruct (lt_eq_lt_dec (maxIndex ll) pli); intuition.
+
exists leader, ll, (findGtIndex es pli), [].
intuition.
*
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
*
simpl; auto.
*
rewrite app_nil_r.
rewrite findGtIndex_removeAfterIndex_commute; eauto using lift_logs_sorted.
unfold ghost_data in *.
simpl in *.
find_rewrite.
eapply findGtIndex_app_1; omega.
*
eauto using findGtIndex_in.
*
left.
intuition.
match goal with | H : forall _, In _ _ -> _ |- _ => apply H end.
find_apply_lem_hyp findAtIndex_elim.
intuition.
subst.
match goal with | _ : In ?x ?l, _ : eIndex ?e > eIndex ?x |- _ => assert (In x (removeAfterIndex l (eIndex e))) by (apply removeAfterIndex_le_In; eauto; omega) end.
unfold ghost_data in *.
simpl in *.
find_rewrite.
do_in_app; intuition.
find_copy_apply_lem_hyp leaderLogs_sorted_invariant; eauto.
find_apply_lem_hyp maxIndex_is_max; eauto; omega.
+
exists leader, ll, (findGtIndex es pli), [].
intuition.
*
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
*
simpl; auto.
*
rewrite app_nil_r.
rewrite findGtIndex_removeAfterIndex_commute; eauto using lift_logs_sorted.
unfold ghost_data in *.
simpl in *.
find_rewrite.
apply findGtIndex_app_1.
omega.
*
eauto using findGtIndex_in.
*
right.
find_apply_lem_hyp findAtIndex_elim.
left.
exists x0.
intuition.
subst.
match goal with | _ : In ?x ?l, _ : eIndex ?e > _ |- _ => assert (In x (removeAfterIndex l (eIndex e))) by (apply removeAfterIndex_le_In; eauto; omega) end.
unfold ghost_data in *.
simpl in *.
find_rewrite.
assert (sorted (es ++ ll)) by (repeat find_reverse_rewrite; apply removeAfterIndex_sorted; repeat find_rewrite; eauto using lift_logs_sorted).
eapply thing3; eauto; try omega.
intros.
match goal with | |- eIndex ?e > _ => assert (In e (log (snd (nwState net h)))) by (unfold ghost_data in *; simpl in *; eapply removeAfterIndex_in; repeat find_reverse_rewrite; eauto) end.
eapply entries_gt_0_invariant; eauto.
+
exists leader, ll, es, (findGtIndex ll pli).
intuition.
*
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
*
apply findGtIndex_Prefix.
*
rewrite findGtIndex_removeAfterIndex_commute; eauto using lift_logs_sorted.
unfold ghost_data in *.
simpl in *.
find_rewrite.
assert (sorted (es ++ ll)) by (repeat find_reverse_rewrite; apply removeAfterIndex_sorted; repeat find_rewrite; eauto using lift_logs_sorted).
apply findGtIndex_app_2; auto.
*
{
right.
left.
find_apply_lem_hyp findAtIndex_elim.
exists x0.
intuition.
-
subst.
match goal with | H : removeAfterIndex _ _ = _ |- _ => find_eapply_lem_hyp removeAfterIndex_le_In; [unfold ghost_data in *; simpl in *; find_rewrite_lem H|omega] end.
assert (sorted (es ++ ll)) by (repeat find_reverse_rewrite; apply removeAfterIndex_sorted; repeat find_rewrite; eauto using lift_logs_sorted).
eapply thing3; eauto; try omega.
intros.
match goal with | |- eIndex ?e > _ => assert (In e (log (snd (nwState net h)))) by (unfold ghost_data in *; simpl in *; eapply removeAfterIndex_in; repeat find_reverse_rewrite; eauto) end.
eapply entries_gt_0_invariant; eauto.
-
left.
intros.
eapply findGtIndex_non_empty; eauto.
}
-
exfalso.
break_exists.
intuition.
find_eapply_lem_hyp nextIndex_sanity; eauto.
break_exists.
unfold ghost_data in *.
simpl in *.
congruence.
}
