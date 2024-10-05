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

Instance lci : leader_completeness_interface.
Proof.
split.
exact leader_completeness_invariant.
