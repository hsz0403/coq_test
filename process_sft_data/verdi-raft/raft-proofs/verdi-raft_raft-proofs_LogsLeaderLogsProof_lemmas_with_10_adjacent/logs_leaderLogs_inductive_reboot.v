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

Lemma logs_leaderLogs_inductive_appendEntriesReply : refined_raft_net_invariant_append_entries_reply logs_leaderLogs_inductive.
Proof using.
red.
unfold logs_leaderLogs_inductive.
intros.
intuition.
-
find_apply_lem_hyp handleAppendEntriesReply_log.
subst.
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *; repeat find_rewrite; find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
-
find_eapply_lem_hyp handleAppendEntriesReply_packets.
subst.
intuition.
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
prove_in.
copy_eapply_prop_hyp In In; eauto.
Admitted.

Lemma logs_leaderLogs_inductive_requestVote : refined_raft_net_invariant_request_vote logs_leaderLogs_inductive.
Proof using.
red.
unfold logs_leaderLogs_inductive.
intros.
intuition.
-
find_apply_lem_hyp handleRequestVote_log.
subst.
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *; repeat find_rewrite; find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_requestVote_leaderLogs; eauto.
-
find_eapply_lem_hyp handleRequestVote_no_append_entries.
subst.
intuition.
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
prove_in.
copy_eapply_prop_hyp In In; eauto.
break_exists_exists; intuition; repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_requestVote_leaderLogs; eauto.
+
find_false.
subst.
simpl in *.
subst.
Admitted.

Lemma logs_leaderLogs_inductive_requestVoteReply : refined_raft_net_invariant_request_vote_reply logs_leaderLogs_inductive.
Proof using.
red.
unfold logs_leaderLogs_inductive.
intros.
intuition.
-
subst.
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *; repeat find_rewrite; [match goal with | H : In _ (log _ ) |- _ => erewrite handleRequestVoteReply_log; eauto; erewrite handleRequestVoteReply_log in H; eauto end|]; find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite ; update_destruct; subst; rewrite_update; eauto; simpl in *; apply update_elections_data_requestVoteReply_leaderLogs; eauto.
-
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
prove_in.
copy_eapply_prop_hyp In In; eauto.
Admitted.

Lemma logs_leaderLogs_inductive_clientRequest : refined_raft_net_invariant_client_request logs_leaderLogs_inductive.
Proof using si lhllsi rri.
red.
unfold logs_leaderLogs_inductive.
intros.
intuition.
-
subst.
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *.
+
find_apply_lem_hyp handleClientRequest_log.
intuition; subst; repeat find_rewrite.
*
find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
*
{
break_exists.
intuition.
repeat find_rewrite.
simpl in *.
intuition; subst.
-
find_apply_lem_hyp leaders_have_leaderLogs_strong_invariant; eauto.
break_exists.
intuition.
unfold ghost_data in *.
simpl in *.
repeat find_rewrite.
match goal with | h : name, _ : _ = ?e :: ?es ++ ?ll |- _ => exists h, ll, (e :: x0) end; intuition.
+
find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
+
break_if; eauto using app_ass; do_bool; omega.
+
simpl in *.
intuition; subst; eauto.
-
find_copy_apply_lem_hyp maxIndex_is_max; eauto using lift_logs_sorted.
find_apply_hyp_hyp.
break_exists_exists; intuition; [find_higher_order_rewrite ; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto|].
break_if; do_bool; intuition; omega.
}
+
find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
-
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
eapply_prop_hyp In pBody; eauto; break_exists_exists; intuition; subst; repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_client_request_leaderLogs; eauto.
+
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp handleClientRequest_no_append_entries; eauto.
intuition.
find_false.
repeat find_rewrite.
Admitted.

Lemma logs_leaderLogs_inductive_timeout : refined_raft_net_invariant_timeout logs_leaderLogs_inductive.
Proof using.
red.
unfold logs_leaderLogs_inductive.
intros.
intuition.
-
find_apply_lem_hyp handleTimeout_log_same.
subst.
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *; repeat find_rewrite; find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_timeout_leaderLogs; eauto.
-
intuition.
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
copy_eapply_prop_hyp In In; eauto.
break_exists_exists; intuition; repeat find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *; rewrite update_elections_data_timeout_leaderLogs; eauto.
+
do_in_map.
subst.
simpl in *.
find_eapply_lem_hyp handleTimeout_packets; eauto.
intuition.
find_false.
repeat find_rewrite.
Admitted.

Lemma logs_leaderLogs_inductive_doGenericServer : refined_raft_net_invariant_do_generic_server logs_leaderLogs_inductive.
Proof using.
red.
unfold logs_leaderLogs_inductive.
intros.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
intuition.
-
find_apply_lem_hyp doGenericServer_log.
unfold logs_leaderLogs in *.
intros.
simpl in *.
find_higher_order_rewrite; update_destruct; subst; rewrite_update; simpl in *; repeat find_rewrite; find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto.
-
find_apply_lem_hyp doGenericServer_packets.
subst.
unfold logs_leaderLogs_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
eapply_prop_hyp In In; eauto.
Admitted.

Lemma doLeader_spec : forall st h os st' ms m t n pli plt es ci, doLeader st h = (os, st', ms) -> In m ms -> snd m = AppendEntries t n pli plt es ci -> t = currentTerm st /\ log st' = log st /\ type st = Leader /\ ((pli = 0 /\ plt = 0 /\ es = findGtIndex (log st) 0) \/ ((exists e, findAtIndex (log st) pli = Some e /\ eTerm e = plt) /\ es = findGtIndex (log st) pli) \/ exists h', pred (getNextIndex st h') <> 0 /\ findAtIndex (log st) (pred (getNextIndex st h')) = None).
Proof using.
intros.
unfold doLeader, advanceCommitIndex in *.
break_match; try solve [find_inversion; simpl in *; intuition].
break_if; try solve [find_inversion; simpl in *; intuition].
find_inversion.
simpl.
do_in_map.
subst.
simpl in *.
find_inversion.
intuition.
match goal with | |- context [pred ?x] => remember (pred x) as index end.
break_match; simpl in *.
-
right.
left.
eauto.
-
destruct index; intuition.
right.
right.
exists x.
match goal with | _ : S _ = pred ?x |- context [pred ?y] => assert (pred x = pred y) by auto end.
repeat find_rewrite.
Admitted.

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
Admitted.

Lemma logs_leaderLogs_inductive_init : refined_raft_net_invariant_init logs_leaderLogs_inductive.
Proof using.
unfold logs_leaderLogs_inductive.
red.
intuition.
-
unfold logs_leaderLogs.
intros.
simpl in *.
intuition.
-
unfold logs_leaderLogs_nw.
intros.
simpl in *.
Admitted.

Lemma logs_leaderLogs_inductive_state_same_packets_subset : refined_raft_net_invariant_state_same_packet_subset logs_leaderLogs_inductive.
Proof using.
red.
unfold logs_leaderLogs_inductive.
intuition.
-
unfold logs_leaderLogs in *.
intros.
repeat find_reverse_higher_order_rewrite.
find_apply_hyp_hyp.
break_exists_exists; intuition.
find_reverse_higher_order_rewrite.
auto.
-
unfold logs_leaderLogs_nw in *.
intros.
find_apply_hyp_hyp.
eapply_prop_hyp pBody pBody; eauto.
Admitted.

Theorem logs_leaderLogs_inductive_invariant : forall net, refined_raft_intermediate_reachable net -> logs_leaderLogs_inductive net.
Proof using lpholli si nisi lhllsi lllmi llci rlmli llsi rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply logs_leaderLogs_inductive_init.
-
apply logs_leaderLogs_inductive_clientRequest.
-
apply logs_leaderLogs_inductive_timeout.
-
apply logs_leaderLogs_inductive_appendEntries.
-
apply logs_leaderLogs_inductive_appendEntriesReply.
-
apply logs_leaderLogs_inductive_requestVote.
-
apply logs_leaderLogs_inductive_requestVoteReply.
-
apply logs_leaderLogs_inductive_doLeader.
-
apply logs_leaderLogs_inductive_doGenericServer.
-
apply logs_leaderLogs_inductive_state_same_packets_subset.
-
Admitted.

Theorem logs_leaderLogs_invariant : forall net, refined_raft_intermediate_reachable net -> logs_leaderLogs net.
Proof using lpholli si nisi lhllsi lllmi llci rlmli llsi rri.
intros.
apply logs_leaderLogs_inductive_invariant.
Admitted.

Theorem logs_leaderLogs_nw_invariant : forall net, refined_raft_intermediate_reachable net -> logs_leaderLogs_nw net.
Proof using lpholli si nisi lhllsi lllmi llci rlmli llsi rri.
intros.
apply logs_leaderLogs_inductive_invariant.
Admitted.

Instance llli : logs_leaderLogs_interface.
Proof.
Admitted.

Lemma logs_leaderLogs_inductive_reboot : refined_raft_net_invariant_reboot logs_leaderLogs_inductive.
Proof using.
red.
unfold logs_leaderLogs_inductive.
intros.
match goal with | H : nwState ?net ?h = (?gd, ?d) |- _ => replace gd with (fst (nwState net h)) in * by (rewrite H; reflexivity); replace d with (snd (nwState net h)) in * by (rewrite H; reflexivity); clear H end.
intuition.
-
subst.
unfold logs_leaderLogs in *.
intros.
repeat find_reverse_higher_order_rewrite.
find_higher_order_rewrite.
update_destruct; subst; rewrite_update; unfold reboot in *; simpl in *; find_apply_hyp_hyp; break_exists_exists; intuition; find_higher_order_rewrite; simpl in *; auto; update_destruct; subst; rewrite_update; simpl in *; auto.
-
unfold logs_leaderLogs_nw in *.
intros.
find_reverse_rewrite.
eapply_prop_hyp pBody pBody; eauto.
break_exists_exists; intuition; subst; repeat find_reverse_higher_order_rewrite; auto; repeat find_higher_order_rewrite; simpl in *; auto; update_destruct; subst; rewrite_update; simpl in *; auto.
