Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.NoAppendEntriesToLeaderInterface.
Require Import VerdiRaft.NoAppendEntriesToSelfInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneLogInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.LogAllEntriesInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.MatchIndexLeaderInterface.
Require Import VerdiRaft.MatchIndexSanityInterface.
Require Import VerdiRaft.AppendEntriesReplySublogInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.MatchIndexAllEntriesInterface.
Section MatchIndexAllEntries.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {naetli : no_append_entries_to_leader_interface}.
Context {naetsi : no_append_entries_to_self_interface}.
Context {taifoli : terms_and_indices_from_one_log_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {laei : log_all_entries_interface}.
Context {aelli : append_entries_leaderLogs_interface}.
Context {lsi : leader_sublog_interface}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {mili : match_index_leader_interface}.
Context {matchisi : match_index_sanity_interface}.
Context {aersi : append_entries_reply_sublog_interface}.
Context {cei : candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Definition match_index_all_entries_nw (net : network) : Prop := forall p t es e, In p (nwPackets net) -> pBody p = AppendEntriesReply t es true -> currentTerm (snd (nwState net (pDst p))) = t -> In e (log (snd (nwState net (pDst p)))) -> eTerm e = t -> eIndex e <= maxIndex es -> type (snd (nwState net (pDst p))) = Leader -> In (t, e) (allEntries (fst (nwState net (pSrc p)))).
Definition match_index_all_entries_inv (net : network) : Prop := match_index_all_entries net /\ match_index_all_entries_nw net.
Instance miaei : match_index_all_entries_interface.
Proof.
constructor.
apply match_index_all_entries_invariant.
End MatchIndexAllEntries.

Lemma match_index_all_entries_append_entries : refined_raft_net_invariant_append_entries' match_index_all_entries_inv.
Proof using ollpti lhllsi lsi aelli laei rlmli taifoli naetsi naetli rri.
unfold refined_raft_net_invariant_append_entries', match_index_all_entries_inv.
simpl.
intros.
break_and.
split.
-
unfold match_index_all_entries in *.
simpl.
intros.
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
+
assert (currentTerm (snd (nwState net (pDst p))) <> t).
{
intro.
match goal with | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] => eapply lifted_no_AE_to_leader with (net := net) in H; eauto end.
eapply handleAppendEntries_leader_was_leader; eauto.
}
find_apply_lem_hyp handleAppendEntries_post_leader_nop; auto.
subst.
eapply_prop_hyp In In; eauto.
repeat find_rewrite.
update_destruct_simplify_hyp; auto using update_elections_data_appendEntries_preserves_allEntries.
+
eapply_prop_hyp In In; eauto.
repeat find_rewrite.
update_destruct_simplify_hyp; auto using update_elections_data_appendEntries_preserves_allEntries.
-
unfold match_index_all_entries_nw.
simpl.
intros.
find_apply_hyp_hyp.
break_or_hyp.
+
unfold match_index_all_entries_nw in *.
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
*
assert (currentTerm (snd (nwState net (pDst p))) <> t).
{
intro.
match goal with | [ H : pBody _ = AppendEntries _ _ _ _ _ _ |- _ ] => eapply lifted_no_AE_to_leader with (net := net) in H; eauto end.
eapply handleAppendEntries_leader_was_leader; eauto.
}
match goal with | [ H : context [handleAppendEntries] |- _ ] => apply handleAppendEntries_post_leader_nop in H; auto end.
subst.
match goal with | [ H : In _ (_ ++ _), H' : forall _ _ _ _, In _ _ -> _ |- _ ] => eapply in_middle_insert in H; eapply H' in H; eauto; try congruence end.
{
update_destruct_simplify_hyp.
-
apply update_elections_data_appendEntries_preserves_allEntries.
repeat find_rewrite.
auto.
-
auto.
}
*
match goal with | [ H : forall _ _ _ _, In _ _ -> _, H' : pBody _ = AppendEntriesReply _ _ _ |- _ ] => eapply H in H'; eauto end.
{
update_destruct_simplify_hyp.
-
apply update_elections_data_appendEntries_preserves_allEntries.
repeat find_rewrite.
auto.
-
auto.
}
+
simpl in *.
find_copy_apply_lem_hyp handleAppendEntries_message.
break_exists.
subst.
find_inversion.
repeat find_higher_order_rewrite.
update_destruct_simplify_hyp.
*
exfalso.
eapply lifted_no_AE_to_self with (net := net); eauto.
*
unfold update_elections_data_appendEntries.
repeat find_rewrite.
simpl.
{
find_copy_apply_lem_hyp handleAppendEntries_success_allEntries.
-
break_exists.
break_and.
find_copy_apply_lem_hyp handleAppendEntries_success_term.
assert (In x (log (snd (nwState net (pSrc p))))).
{
eapply appendEntries_sublog; eauto.
subst.
repeat find_rewrite.
auto.
}
assert (entries_match (log d) (log (snd (nwState net (pSrc p))))).
{
match goal with | [ H : refined_raft_intermediate_reachable (mkNetwork ?a ?b) |- _ ] => let H' := fresh "H" in pose proof entries_match_invariant _ (pDst p) (pSrc p) H as H'; simpl in H'; repeat find_higher_order_rewrite; rewrite_update; simpl in H'; auto end.
}
assert (In e (log d)) as Helogd.
{
match goal with | [ H : entries_match _ _ |- _ ] => specialize (H x x e) end.
assert (eIndex e <= eIndex x) by omega.
repeat concludes.
intuition.
}
match goal with | [ H : refined_raft_intermediate_reachable (mkNetwork ?a ?b) |- _ ] => let H' := fresh "H" in pose proof log_all_entries_invariant _ H (pDst p) e as H'; simpl in H'; repeat find_higher_order_rewrite; rewrite_update; simpl in H'; unfold update_elections_data_appendEntries in H'; repeat find_rewrite; simpl in H' end.
auto.
-
find_apply_lem_hyp lifted_terms_and_indices_from_one_log; auto.
break_and.
apply maxIndex_gt_0_nonempty.
omega.
-
intros.
match goal with | [ H : refined_raft_intermediate_reachable (mkNetwork _ _) |- _ ] => clear H end.
pose proof entries_match_nw_host_invariant _ ltac:(eauto) _ _ _ _ _ _ _ (pDst p) e0 e' e'' ltac:(eauto) ltac:(eauto).
repeat find_rewrite.
auto.
-
apply entries_sorted_invariant.
auto.
}
