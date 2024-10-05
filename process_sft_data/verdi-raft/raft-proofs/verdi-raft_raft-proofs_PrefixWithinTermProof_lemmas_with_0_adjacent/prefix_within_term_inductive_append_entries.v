Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.PrefixWithinTermInterface.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.LeaderLogsSublogInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.AllEntriesLogMatchingInterface.
Require Import VerdiRaft.AppendEntriesRequestTermSanityInterface.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Section PrefixWithinTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {llli : logs_leaderLogs_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {llsli : leaderLogs_sublog_interface}.
Context {lsli : leader_sublog_interface}.
Context {nisi : nextIndex_safety_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {aelmi : allEntries_log_matching_interface}.
Context {aertsi : append_entries_request_term_sanity_interface}.
Context {aelsi : allEntries_leader_sublog_interface}.
Definition lift_leader_sublog : forall net leader e h, refined_raft_intermediate_reachable net -> type (snd (nwState net leader)) = Leader -> In e (log (snd (nwState net h))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Proof using lsli rri.
intros.
pose proof lift_prop leader_sublog_host_invariant.
conclude_using ltac:(apply leader_sublog_invariant_invariant).
find_apply_hyp_hyp.
match goal with | H : leader_sublog_host_invariant _ |- _ => specialize (H leader e h) end.
repeat find_rewrite_lem deghost_spec.
intuition.
Definition lift_leader_sublog_nw : forall net leader p t leaderId prevLogIndex prevLogTerm entries leaderCommit e, refined_raft_intermediate_reachable net -> type (snd (nwState net leader)) = Leader -> In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> In e entries -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Proof using lsli rri.
intros.
pose proof lift_prop leader_sublog_nw_invariant.
conclude_using ltac:(apply leader_sublog_invariant_invariant).
find_apply_hyp_hyp.
find_apply_lem_hyp exists_deghosted_packet.
match goal with | H : exists _, _ |- _ => destruct H as [q] end.
break_and.
match goal with | H : leader_sublog_nw_invariant _ |- _ => specialize (H leader q t leaderId prevLogIndex prevLogTerm entries leaderCommit e) end.
repeat find_rewrite_lem deghost_spec.
subst.
simpl in *.
intuition.
Definition append_entries_append_entries_prefix_within_term_nw net := forall p t n pli plt es ci p' t' n' pli' plt' es' ci' e e', In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In p' (nwPackets net) -> pBody p' = AppendEntries t' n' pli' plt' es' ci' -> eTerm e = eTerm e' -> eIndex e <= eIndex e' -> In e es -> In e' es' -> (In e es' \/ (eIndex e = pli' /\ eTerm e = plt') \/ (eIndex e < pli' /\ eTerm e <= plt')).
Definition locked_or x y := x \/ y.
Definition log_leaderLogs_prefix_within_term net := forall h t ll leader, In (t, ll) (leaderLogs (fst (nwState net leader))) -> prefix_within_term (log (snd (nwState net h))) ll.
Definition allEntries_log_prefix_within_term net := forall h h', prefix_within_term (map snd (allEntries (fst (nwState net h)))) (log (snd (nwState net h'))).
Definition allEntries_append_entries_prefix_within_term_nw net := forall p t n pli plt es ci h e e', In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> eTerm e = eTerm e' -> eIndex e <= eIndex e' -> In e (map snd (allEntries (fst (nwState net h)))) -> In e' es -> (In e es \/ (eIndex e = pli /\ eTerm e = plt) \/ (eIndex e < pli /\ eTerm e <= plt)).
Definition append_entries_leaderLogs_prefix_within_term net := forall p t n pli plt es ci h t' ll, In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> In (t', ll) (leaderLogs (fst (nwState net h))) -> prefix_within_term es ll.
Definition append_entries_log_prefix_within_term net := forall p t n pli plt es ci h, In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> prefix_within_term es (log (snd (nwState net h))).
Definition prefix_within_term_inductive net := allEntries_leaderLogs_prefix_within_term net /\ log_leaderLogs_prefix_within_term net /\ allEntries_log_prefix_within_term net /\ allEntries_append_entries_prefix_within_term_nw net /\ append_entries_leaderLogs_prefix_within_term net /\ append_entries_log_prefix_within_term net.
Instance pwti : prefix_within_term_interface.
split; intros.
-
apply prefix_within_term_inductive_invariant.
auto.
-
apply log_log_prefix_within_term_invariant.
auto.
Defined.
End PrefixWithinTerm.

Lemma prefix_within_term_inductive_append_entries : refined_raft_net_invariant_append_entries prefix_within_term_inductive.
Proof using aertsi aelmi llsi ollpti rlmli llli.
red.
unfold prefix_within_term_inductive.
intuition.
-
unfold allEntries_leaderLogs_prefix_within_term.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_appendEntries_leaderLogs; eauto; solve [ eapply prefix_within_term_union; [|idtac|eapply update_elections_data_appendEntries_allEntries; eauto]; eauto].
-
unfold log_leaderLogs_prefix_within_term.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_appendEntries_leaderLogs; eauto; find_apply_lem_hyp handleAppendEntries_log; intuition; repeat find_rewrite; eauto; match goal with | |- context [?es ++ removeAfterIndex ?l _] => eapply prefix_within_term_union with (l1' := es) (l1'' := l) end; eauto; intros; do_in_app; intuition; eauto using removeAfterIndex_in.
-
unfold allEntries_log_prefix_within_term.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_appendEntries_leaderLogs; eauto; find_apply_lem_hyp handleAppendEntries_log; intuition; subst; repeat find_rewrite; try solve [ eapply prefix_within_term_union; [|idtac|solve[eapply update_elections_data_appendEntries_allEntries; eauto]]; eauto].
Unshelve.
all:eauto.
+
unfold prefix_within_term, allEntries_append_entries_prefix_within_term_nw in *.
intros.
find_apply_lem_hyp update_elections_data_appendEntries_allEntries.
intuition.
eapply_prop_hyp pBody pBody; eauto.
intuition; try omega.
find_apply_lem_hyp allEntries_gt_0_invariant; eauto.
omega.
+
unfold prefix_within_term, allEntries_append_entries_prefix_within_term_nw in *.
intros.
find_apply_lem_hyp update_elections_data_appendEntries_allEntries.
intuition.
do_in_app.
intuition.
*
{
copy_eapply_prop_hyp pBody pBody; eauto.
intuition.
-
subst.
apply in_app_iff.
right.
apply removeAfterIndex_le_In; auto.
break_exists.
intuition.
assert (x = e) by (eapply allEntries_log_matching_invariant; eauto).
subst.
auto.
-
break_exists.
intuition.
subst.
match goal with | _ : eIndex ?e < eIndex ?x |- _ => destruct (lt_eq_lt_dec (eTerm e) (eTerm x)) end; intuition; try omega.
+
exfalso.
eapply append_entries_request_term_sanity_invariant in H1; eauto.
conclude_using eauto; omega.
+
apply in_app_iff.
right.
apply removeAfterIndex_le_In; [omega|].
eapply_prop allEntries_log_prefix_within_term; eauto; omega.
}
*
find_copy_apply_lem_hyp removeAfterIndex_in; find_apply_lem_hyp removeAfterIndex_In_le; [|eapply entries_sorted_invariant; eauto].
apply in_app_iff; right.
apply removeAfterIndex_le_In; eauto; try omega.
eapply_prop allEntries_log_prefix_within_term; eauto.
+
unfold prefix_within_term, allEntries_append_entries_prefix_within_term_nw in *.
intros.
eapply_prop_hyp pBody pBody; eauto.
intuition; try omega.
find_apply_lem_hyp allEntries_gt_0_invariant; eauto.
omega.
+
unfold prefix_within_term, allEntries_append_entries_prefix_within_term_nw in *.
intros.
do_in_app.
intuition.
*
{
copy_eapply_prop_hyp pBody pBody; eauto.
intuition.
-
subst.
apply in_app_iff.
right.
apply removeAfterIndex_le_In; auto.
break_exists.
intuition.
assert (x = e) by (eapply allEntries_log_matching_invariant; eauto).
subst.
auto.
-
break_exists.
intuition.
subst.
match goal with | _ : eIndex ?e < eIndex ?x |- _ => destruct (lt_eq_lt_dec (eTerm e) (eTerm x)) end; intuition; try omega.
+
exfalso.
eapply append_entries_request_term_sanity_invariant in H1; eauto.
conclude_using eauto.
omega.
+
apply in_app_iff.
right.
apply removeAfterIndex_le_In; [omega|].
eapply_prop allEntries_log_prefix_within_term; eauto; omega.
}
*
find_copy_apply_lem_hyp removeAfterIndex_in; find_apply_lem_hyp removeAfterIndex_In_le; [|eapply entries_sorted_invariant; eauto].
apply in_app_iff; right.
apply removeAfterIndex_le_In; eauto; try omega.
eapply_prop allEntries_log_prefix_within_term; eauto.
-
unfold allEntries_append_entries_prefix_within_term_nw.
intros.
simpl in *.
subst.
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_appendEntries_leaderLogs; eauto.
+
find_apply_lem_hyp update_elections_data_appendEntries_allEntries.
intuition.
*
eapply_prop_hyp allEntries_append_entries_prefix_within_term_nw In; try eapply H13; eauto; repeat find_rewrite; intuition.
find_apply_hyp_hyp.
intuition; [in_crush|].
subst.
simpl in *.
subst.
unfold handleAppendEntries in *.
repeat break_match; find_inversion; congruence.
*
find_eapply_lem_hyp append_entries_append_entries_prefix_within_term_invariant.
conclude_using eauto.
find_rewrite.
eapply H0.
5: {
eauto.
}
all:eauto.
find_apply_hyp_hyp.
intuition; [find_rewrite; in_crush|].
repeat (subst; simpl in *).
unfold handleAppendEntries in *; repeat break_match; find_inversion; congruence.
+
find_apply_hyp_hyp.
intuition.
*
copy_eapply_prop_hyp allEntries_append_entries_prefix_within_term_nw pBody; [|repeat find_rewrite; in_crush].
repeat conclude_using eauto.
repeat find_rewrite.
intuition.
*
exfalso.
subst.
simpl in *.
subst.
unfold handleAppendEntries in *; repeat break_match; find_inversion; congruence.
-
unfold append_entries_leaderLogs_prefix_within_term.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition; [|subst; simpl in *; subst; unfold handleAppendEntries in *; repeat break_match; find_inversion; congruence].
repeat find_higher_order_rewrite.
repeat destruct_update; simpl in *; eauto; try find_rewrite_lem update_elections_data_appendEntries_leaderLogs; eauto.
-
unfold append_entries_log_prefix_within_term.
intros.
simpl in *.
subst.
find_apply_hyp_hyp.
intuition; [| subst; simpl in *; subst; unfold handleAppendEntries in *; repeat break_match; find_inversion; congruence].
find_higher_order_rewrite.
destruct_update; simpl in *; eauto.
find_apply_lem_hyp handleAppendEntries_log.
intuition; subst; repeat find_rewrite; eauto.
+
unfold prefix_within_term.
intros.
find_copy_apply_lem_hyp append_entries_append_entries_prefix_within_term_invariant.
match goal with | H : append_entries_append_entries_prefix_within_term_nw _, _ : pBody ?p = AppendEntries ?t ?n ?pli ?plt ?es ?ci, _ : pBody ?p' = AppendEntries ?t' ?n' ?pli' ?plt' ?es' ?ci', _ : In ?e' ?es', _ : In ?e ?es |- In ?e ?es' => specialize (H p t n pli plt es ci p' t' n' pli' plt' es' ci' e e') end.
conclude_using ltac:(repeat find_rewrite; in_crush).
concludes.
conclude_using ltac:(repeat find_rewrite; in_crush).
repeat concludes.
intuition.
*
exfalso.
match goal with | _ : eIndex ?e = 0 |- _ => cut (eIndex e > 0); [intuition|] end.
eapply entries_gt_0_nw_invariant; [|idtac|idtac|eauto]; [|idtac|eauto]; eauto.
*
omega.
+
{
unfold prefix_within_term.
intros.
do_in_app.
intuition.
-
find_copy_apply_lem_hyp append_entries_append_entries_prefix_within_term_invariant.
match goal with | H : append_entries_append_entries_prefix_within_term_nw _, _ : pBody ?p = AppendEntries ?t ?n ?pli ?plt ?es ?ci, _ : pBody ?p' = AppendEntries ?t' ?n' ?pli' ?plt' ?es' ?ci', _ : In ?e' ?es', _ : In ?e ?es |- In ?e (?es' ++ _) => specialize (H p t n pli plt es ci p' t' n' pli' plt' es' ci' e e') end.
conclude_using ltac:(repeat find_rewrite; in_crush).
concludes.
conclude_using ltac:(repeat find_rewrite; in_crush).
repeat concludes.
intuition.
+
break_exists.
intuition.
subst.
apply in_app_iff.
right.
apply removeAfterIndex_le_In; auto.
eapply entries_match_nw_host_invariant.
8: {
eauto.
}
3: {
eauto.
}
all:eauto.
+
find_eapply_lem_hyp append_entries_request_term_sanity_invariant; eauto.
repeat find_rewrite.
match goal with | _ : ?x >= ?y, _ : ?x <= ?y |- _ => assert (x = y) by eauto using le_antisym end.
subst.
break_exists.
intuition.
subst.
apply in_app_iff.
right.
apply removeAfterIndex_le_In; auto; [omega|].
eapply_prop append_entries_log_prefix_within_term.
6: {
eauto.
}
5: {
eauto.
}
2: {
eauto.
}
all:eauto; repeat find_rewrite; intuition.
-
apply in_app_iff.
right.
find_copy_apply_lem_hyp removeAfterIndex_in.
find_apply_lem_hyp removeAfterIndex_In_le; [|eapply entries_sorted_invariant; eauto].
eapply removeAfterIndex_le_In; [omega|].
eapply_prop append_entries_log_prefix_within_term.
6: {
eauto.
}
5: {
eauto.
}
2: {
eauto.
}
all:eauto.
}
