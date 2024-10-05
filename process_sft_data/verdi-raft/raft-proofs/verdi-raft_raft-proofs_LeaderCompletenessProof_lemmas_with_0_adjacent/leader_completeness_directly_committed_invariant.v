Require Import Sumbool.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.RefinementCommonDefinitions.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.PrefixWithinTermInterface.
Require Import VerdiRaft.LeaderLogsTermSanityInterface.
Require Import VerdiRaft.LeaderLogsPreservedInterface.
Require Import VerdiRaft.EveryEntryWasCreatedInterface.
Require Import VerdiRaft.LeaderLogsVotesWithLogInterface.
Require Import VerdiRaft.AllEntriesVotesWithLogInterface.
Require Import VerdiRaft.VotesWithLogSortedInterface.
Require Import VerdiRaft.TermsAndIndicesFromOneInterface.
Require Import VerdiRaft.LeaderLogsLogMatchingInterface.
Section LeaderCompleteness.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {pwti : prefix_within_term_interface}.
Context {lltsi : leaderLogs_term_sanity_interface}.
Context {llpi : leaderLogs_preserved_interface}.
Context {eewci : every_entry_was_created_interface}.
Context {llvwli : leaderLogs_votesWithLog_interface}.
Context {aevwli : allEntries_votesWithLog_interface}.
Context {vwlsi : votesWithLog_sorted_interface}.
Context {taifoi : terms_and_indices_from_one_interface}.
Context {lllmi : leaderLogs_entries_match_interface}.
Fixpoint contradicting_leader_logs_on_leader l t e := match l with | (t', log') :: l' => if (sumbool_and _ _ _ _ (lt_dec t t') (sumbool_not _ _ (in_dec entry_eq_dec e log'))) then (t', log') :: contradicting_leader_logs_on_leader l' t e else contradicting_leader_logs_on_leader l' t e | [] => [] end.
Fixpoint contradicting_leader_logs net nodes t e : list (term * name * list entry) := match nodes with | h :: nodes' => (map (fun l => (fst l, h, snd l)) (contradicting_leader_logs_on_leader (leaderLogs (fst (nwState net h))) t e)) ++ contradicting_leader_logs net nodes' t e | [] => [] end.
Definition minimal_contradicting_leader_log net t e := argmin (fun l => fst (fst l)) (contradicting_leader_logs net nodes t e).
Instance lci : leader_completeness_interface.
Proof.
split.
exact leader_completeness_invariant.
End LeaderCompleteness.

Theorem leader_completeness_directly_committed_invariant : forall net, refined_raft_intermediate_reachable net -> leader_completeness_directly_committed net.
Proof using taifoi vwlsi aevwli llvwli eewci llpi lltsi pwti.
unfold leader_completeness_directly_committed in *.
intros.
unfold directly_committed in *.
destruct (minimal_contradicting_leader_log net (eTerm e) e) eqn:?; eauto using minimal_contradicting_leader_log_None.
repeat destruct p.
find_apply_lem_hyp minimal_contradicting_leader_log_elim.
match goal with | [ H : exists _, _ |- _ ] => destruct H as [quorum] end.
intuition.
destruct (le_lt_dec n t).
-
exfalso.
assert (forall e', In e' l -> (eTerm e' < eTerm e) \/ (eTerm e' = eTerm e /\ eIndex e' < eIndex e)).
{
intros.
destruct (lt_eq_lt_dec (eTerm e') (eTerm e)).
-
intuition.
destruct (le_lt_dec (eIndex e) (eIndex e')); auto.
assert (exists x, In x quorum).
{
destruct quorum.
-
simpl in *.
omega.
-
simpl.
eauto.
}
break_exists.
assert (prefix_within_term (map snd (allEntries (fst (nwState net x)))) l) by (eapply allEntries_leaderLogs_prefix_within_term_invariant; eauto).
unfold prefix_within_term in *.
exfalso.
find_false.
match goal with | [ H : _ |- _ ] => eapply H; try eassumption; auto; [apply in_map_iff; eexists; split; [|eauto]; auto] end.
-
assert (leaderLogs_term_sanity net) by eauto using leaderLogs_term_sanity_invariant.
unfold leaderLogs_term_sanity in *.
assert (eTerm e' < n) by eauto.
assert (every_entry_was_created net) by eauto using every_entry_was_created_invariant.
unfold every_entry_was_created in *.
find_insterU.
find_insterU.
find_insterU.
find_insterU.
conclude_using eauto.
conclude_using eauto.
unfold term_was_created in *.
break_exists.
find_copy_apply_hyp_hyp.
repeat break_or_hyp; try omega.
assert (leaderLogs_preserved net) by eauto using leaderLogs_preserved_invariant.
unfold leaderLogs_preserved in *.
exfalso.
eauto.
}
assert (leaderLogs_votesWithLog net) by eauto using leaderLogs_votesWithLog_invariant.
unfold leaderLogs_votesWithLog in *.
find_apply_hyp_hyp.
match goal with | [ H : exists _, _ |- _ ] => destruct H as [quorum'] end.
break_and.
assert (NoDup nodes) by eauto using all_fin_NoDup.
match goal with | H : NoDup nodes, _ : NoDup ?l1, _ : NoDup ?l2 |- _ => eapply pigeon with (l := nodes) (sub1 := l1) (sub2 := l2) in H end; eauto using all_fin_all, name_eq_dec, div2_correct.
match goal with | [ H : exists _, _ |- _ ] => destruct H as [a] end.
break_and.
find_apply_hyp_hyp.
find_apply_hyp_hyp.
break_exists.
break_and.
assert (In e x).
{
assert (allEntries_votesWithLog net) by eauto using allEntries_votesWithLog_invariant.
unfold allEntries_votesWithLog in *.
eapply_prop_hyp In In; eauto.
break_or_hyp; auto.
break_exists.
break_and.
match goal with | [ H : context [ In _ _ -> _ \/ _ ], H' : In _ _ |- _ ] => eapply H in H' end.
repeat (try break_or_hyp; break_and); try omega.
congruence.
}
assert (sorted x) by (eapply votesWithLog_sorted_invariant; eauto).
assert (maxTerm x >= eTerm e) by eauto using maxTerm_is_max.
assert (maxIndex x >= eIndex e) by eauto using maxIndex_is_max.
assert (exists e', In e' l /\ eTerm e' = maxTerm l /\ eIndex e' = maxIndex l).
{
assert (eTerm e >= 1 /\ eIndex e >= 1) by match goal with | [ H : In _ (votesWithLog _) |- _ ] => solve [eapply terms_and_indices_from_one_invariant in H; eauto] end.
destruct l.
-
simpl in *.
unfold moreUpToDate in *.
do_bool.
repeat (intuition; do_bool); try omega.
-
simpl in *.
eauto.
}
match goal with | [ H : exists _, _ |- _ ] => destruct H as [e'] end.
break_and.
find_apply_hyp_hyp.
unfold moreUpToDate in *.
do_bool; repeat (try break_or_hyp; break_and; do_bool); omega.
-
match goal with | [ H : context [In], H' : context [In] |- _ ] => apply H in H'; intuition; omega end.
