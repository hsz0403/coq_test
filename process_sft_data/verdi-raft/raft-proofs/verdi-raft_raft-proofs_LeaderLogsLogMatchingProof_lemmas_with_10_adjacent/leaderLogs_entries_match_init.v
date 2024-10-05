Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LeaderLogsSublogInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Section LeaderLogsLogMatching.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lmi : log_matching_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {si : sorted_interface}.
Context {llsli : leaderLogs_sublog_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {taifoi : terms_and_indices_from_one_interface}.
Definition leaderLogs_entries_match_nw (net : network) : Prop := forall h llt ll p t src pli plt es ci, In (llt, ll) (leaderLogs (fst (nwState net h))) -> In p (nwPackets net) -> pBody p = AppendEntries t src pli plt es ci -> (forall e1 e2, eIndex e1 = eIndex e2 -> eTerm e1 = eTerm e2 -> In e1 es -> In e2 ll -> (forall e3, eIndex e3 <= eIndex e1 -> In e3 es -> In e3 ll) /\ (pli <> 0 -> exists e4, eIndex e4 = pli /\ eTerm e4 = plt /\ In e4 ll)).
Definition leaderLogs_entries_match (net : network) : Prop := leaderLogs_entries_match_host net /\ leaderLogs_entries_match_nw net.
Ltac use_log_matching_nw := pose proof (lifted_log_matching_nw _ ltac:(eauto)); match goal with | [ H : _ |- _ ] => eapply H; [|eauto]; repeat find_rewrite; intuition end.
Instance lllmi : leaderLogs_entries_match_interface : Prop.
Proof.
split.
apply leaderLogs_entries_match_invariant.
End LeaderLogsLogMatching.

Lemma entries_match_cons_gt_maxTerm : forall x xs ys, sorted xs -> sorted ys -> eIndex x > maxIndex xs -> eTerm x > maxTerm ys -> entries_match xs ys -> entries_match (x :: xs) ys.
Proof using.
unfold entries_match.
intuition; simpl in *; intuition; subst; subst; try match goal with | [ H : In _ _ |- _ ] => apply maxTerm_is_max in H; [| solve[auto]]; omega | [ H : In _ _ |- _ ] => apply maxIndex_is_max in H; [| solve[auto]]; omega end.
-
match goal with | [ H : _ |- _ ] => solve [eapply H; eauto] end.
-
right.
Admitted.

Lemma entries_match_cons_sublog : forall x xs ys, sorted xs -> sorted ys -> eIndex x > maxIndex xs -> entries_match xs ys -> (forall y, In y ys -> eTerm x = eTerm y -> In y xs) -> entries_match (x :: xs) ys.
Proof using.
unfold entries_match.
intuition; simpl in *; intuition; subst; subst; try solve [ exfalso; try find_apply_hyp_hyp; match goal with | [ H : In _ _ |- _ ] => apply maxIndex_is_max in H; [| solve[auto]]; omega end].
-
match goal with | [ H : _ |- _ ] => solve [eapply H; eauto] end.
-
right.
Admitted.

Lemma entries_match_nil : forall l, entries_match l [].
Proof using.
red.
simpl.
Admitted.

Lemma lifted_logs_sorted_nw : forall net p t n plt plti es ci, refined_raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n plt plti es ci -> sorted es.
Proof using si rri.
intros.
pose proof (lift_prop _ logs_sorted_invariant).
find_insterU.
conclude_using eauto.
unfold logs_sorted in *.
break_and.
unfold logs_sorted_nw in *.
eapply H3.
-
unfold deghost.
simpl.
apply in_map_iff.
eauto.
-
simpl.
Admitted.

Lemma lifted_logs_sorted_host : forall net h , refined_raft_intermediate_reachable net -> sorted (log (snd (nwState net h))).
Proof using si rri.
intros.
pose proof (lift_prop _ logs_sorted_invariant).
find_insterU.
conclude_using eauto.
unfold logs_sorted in *.
break_and.
unfold logs_sorted_host in *.
find_insterU.
find_rewrite_lem deghost_spec.
Admitted.

Lemma leaderLogs_entries_match_nw_packet_set : forall net net', leaderLogs_entries_match_nw net -> (forall p, In p (nwPackets net') -> is_append_entries (pBody p) -> In p (nwPackets net)) -> (forall h, leaderLogs (fst (nwState net' h)) = leaderLogs (fst (nwState net h))) -> leaderLogs_entries_match_nw net'.
Proof using.
unfold leaderLogs_entries_match_nw.
intros.
eapply_prop_hyp In nwPackets; [|eauto 10].
Admitted.

Lemma leaderLogs_entries_match_host_state_same : forall net net', leaderLogs_entries_match_host net -> (forall h, leaderLogs (fst (nwState net' h)) = leaderLogs (fst (nwState net h))) -> (forall h, log (snd (nwState net' h)) = log (snd (nwState net h))) -> leaderLogs_entries_match_host net'.
Proof using.
unfold leaderLogs_entries_match_host.
intuition.
repeat find_higher_order_rewrite.
Admitted.

Lemma handleClientRequest_no_send : forall h st client id c out st' ms, handleClientRequest h st client id c = (out, st', ms) -> ms = [].
Proof using.
unfold handleClientRequest.
intros.
Admitted.

Lemma leaderLogs_entries_match_client_request : refined_raft_net_invariant_client_request leaderLogs_entries_match.
Proof using llsli si llsi lltsi rri.
unfold refined_raft_net_invariant_client_request, leaderLogs_entries_match.
intros.
split.
-
{
unfold leaderLogs_entries_match_host.
simpl.
intuition.
subst.
repeat find_higher_order_rewrite.
repeat update_destruct_simplify.
-
find_rewrite_lem update_elections_data_client_request_leaderLogs.
destruct (log d) using (handleClientRequest_log_ind ltac:(eauto)).
+
eauto.
+
destruct ll.
*
apply entries_match_nil.
*
{
apply entries_match_cons_gt_maxTerm; eauto.
-
eauto using lifted_logs_sorted_host.
-
eapply leaderLogs_sorted_invariant; eauto.
-
omega.
-
find_copy_apply_lem_hyp leaderLogs_currentTerm_invariant; auto.
find_copy_apply_lem_hyp leaderLogs_term_sanity_invariant.
unfold leaderLogs_term_sanity in *.
eapply_prop_hyp In In; simpl; eauto.
repeat find_rewrite.
simpl in *.
omega.
}
-
destruct (log d) using (handleClientRequest_log_ind ltac:(eauto)).
+
eauto.
+
apply entries_match_cons_sublog; eauto.
*
eauto using lifted_logs_sorted_host.
*
eapply leaderLogs_sorted_invariant; eauto.
*
omega.
*
intros.
eapply leaderLogs_sublog_invariant; eauto.
simpl in *.
congruence.
-
find_rewrite_lem update_elections_data_client_request_leaderLogs.
eauto.
-
eauto.
}
-
eapply leaderLogs_entries_match_nw_packet_set with (net:=net); intuition.
+
find_apply_hyp_hyp.
intuition eauto.
erewrite handleClientRequest_no_send with (ms := l) in * by eauto.
simpl in *.
intuition.
+
simpl.
subst.
find_higher_order_rewrite.
rewrite update_fun_comm.
simpl.
rewrite update_fun_comm.
simpl.
rewrite update_elections_data_client_request_leaderLogs.
Admitted.

Lemma leaderLogs_entries_match_timeout : refined_raft_net_invariant_timeout leaderLogs_entries_match.
Proof using.
unfold refined_raft_net_invariant_timeout, leaderLogs_entries_match.
intuition.
-
eapply leaderLogs_entries_match_host_state_same; eauto; simpl; intros; subst; find_higher_order_rewrite; repeat update_destruct_simplify; rewrite_update; auto; try rewrite update_elections_data_timeout_leaderLogs; try erewrite handleTimeout_log_same by eauto; eauto.
-
eapply leaderLogs_entries_match_nw_packet_set with (net:=net); intuition.
+
simpl in *.
find_apply_hyp_hyp.
intuition.
do_in_map.
subst.
simpl in *.
exfalso.
eapply handleTimeout_not_is_append_entries; eauto 10.
+
simpl.
repeat find_higher_order_rewrite.
rewrite update_fun_comm.
simpl.
rewrite update_fun_comm.
simpl.
rewrite update_elections_data_timeout_leaderLogs.
Admitted.

Lemma leaderLogs_entries_match_init : refined_raft_net_invariant_init leaderLogs_entries_match.
Proof using.
unfold refined_raft_net_invariant_init, leaderLogs_entries_match, leaderLogs_entries_match_host, leaderLogs_entries_match_nw.
simpl.
intuition.
