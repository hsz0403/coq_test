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

Lemma match_index_all_entries_append_entries_reply : refined_raft_net_invariant_append_entries_reply match_index_all_entries_inv.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, match_index_all_entries_inv.
simpl.
intros.
split.
-
{
unfold match_index_all_entries in *.
simpl.
intros.
break_and.
repeat find_higher_order_rewrite.
rewrite update_nop_fst.
update_destruct_simplify_hyp.
-
find_copy_apply_lem_hyp handleAppendEntriesReply_spec.
intuition.
+
match goal with | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h) end.
repeat find_rewrite.
repeat concludes.
find_erewrite_lem handleAppendEntriesReply_log.
auto.
+
congruence.
+
repeat find_rewrite.
match goal with | [ H : context [ assoc_default _ (assoc_set _ _ ?x _) ?y _ ] |- _ ] => destruct (name_eq_dec x y) end.
*
subst.
rewrite get_set_same_default in *.
find_apply_lem_hyp app_cons_in.
find_erewrite_lem handleAppendEntriesReply_log.
{
find_apply_lem_hyp PeanoNat.Nat.max_le.
break_or_hyp.
-
match goal with | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) (pSrc p)) end.
repeat find_rewrite.
auto.
-
unfold match_index_all_entries_nw in *.
match goal with | [ H : pBody _ = _, H' : _ |- _ ] => eapply H' with (e := e) in H; auto end.
}
*
rewrite get_set_diff_default in * by auto.
match goal with | [ H : forall _ _ _, type _ = _ -> _ |- _ ] => specialize (H e (pDst p) h) end.
repeat find_rewrite.
repeat concludes.
find_erewrite_lem handleAppendEntriesReply_log.
auto.
-
find_apply_hyp_hyp.
congruence.
}
-
break_and.
unfold match_index_all_entries_nw in *.
simpl.
intros.
repeat find_higher_order_rewrite.
rewrite update_nop_fst.
find_apply_hyp_hyp.
break_or_hyp.
+
update_destruct_simplify_hyp.
*
find_erewrite_lem handleAppendEntriesReply_log.
find_copy_apply_lem_hyp handleAppendEntriesReply_spec.
{
repeat break_or_hyp; break_and.
-
repeat find_rewrite.
eauto using in_middle_insert.
-
congruence.
-
repeat find_rewrite.
eauto using in_middle_insert.
}
*
eauto using in_middle_insert.
+
do_in_map.
find_apply_lem_hyp handleAppendEntriesReply_packets.
subst.
simpl in *.
intuition.
