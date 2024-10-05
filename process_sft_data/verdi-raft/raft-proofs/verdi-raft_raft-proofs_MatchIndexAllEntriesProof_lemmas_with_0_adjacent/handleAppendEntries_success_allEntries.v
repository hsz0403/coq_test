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

Lemma handleAppendEntries_success_allEntries : forall h st t n pli plt es ci st' t', handleAppendEntries h st t n pli plt es ci = (st', AppendEntriesReply t' es true) -> es <> nil -> (forall e e' e'', In e es -> In e' (log st) -> eIndex e = eIndex e' -> eTerm e = eTerm e' -> In e'' es -> eIndex e'' <= eIndex e -> In e'' (log st)) -> sorted (log st) -> exists e, In e (log st') /\ In e es /\ eIndex e = maxIndex es /\ eTerm e = maxTerm es.
Proof using.
unfold handleAppendEntries, haveNewEntries.
intros.
break_if; try find_inversion.
break_if.
-
break_if; find_inversion; simpl; repeat (do_bool; repeat break_and).
+
find_apply_lem_hyp not_empty_true_elim.
pose proof maxIndex_non_empty es ltac:(auto).
break_exists_exists.
intuition.
+
break_or_hyp.
*
find_apply_lem_hyp not_empty_false_elim.
congruence.
*
break_match; try discriminate.
do_bool.
rewrite advanceCurrentTerm_log.
find_apply_lem_hyp findAtIndex_elim.
break_and.
pose proof maxIndex_non_empty es ltac:(auto).
break_exists_name e'.
break_and.
match goal with | [ H : forall _ _ _, In _ _ -> _ |- _ ] => specialize (H e' e e') end.
repeat find_rewrite.
repeat concludes.
intuition.
assert (e = e').
{
eapply uniqueIndices_elim_eq; eauto.
auto using sorted_uniqueIndices.
}
subst.
eauto.
-
break_match; try find_inversion.
break_if; try find_inversion.
break_if; find_inversion; simpl; repeat (do_bool; repeat break_and).
+
find_apply_lem_hyp not_empty_true_elim.
pose proof maxIndex_non_empty es ltac:(auto).
break_exists_exists.
intuition.
+
break_or_hyp.
*
find_apply_lem_hyp not_empty_false_elim.
congruence.
*
break_match; try discriminate.
do_bool.
rewrite advanceCurrentTerm_log.
find_apply_lem_hyp findAtIndex_elim.
break_and.
pose proof maxIndex_non_empty es ltac:(auto).
break_exists_name e'.
break_and.
match goal with | [ H : forall _ _ _, In _ _ -> _ |- _ ] => specialize (H e' e0 e') end.
repeat find_rewrite.
repeat concludes.
intuition.
assert (e0 = e').
{
eapply uniqueIndices_elim_eq; eauto.
auto using sorted_uniqueIndices.
}
subst.
eauto.
