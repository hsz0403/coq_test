Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.LogsLeaderLogsInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.AllEntriesLeaderLogsTermInterface.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.OneLeaderLogPerTermInterface.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.AllEntriesTermSanityInterface.
Require Import VerdiRaft.AllEntriesLogInterface.
Section AllEntriesLog.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {llli : logs_leaderLogs_interface}.
Context {aerlli : append_entries_leaderLogs_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Context {aellti : allEntries_leaderLogs_term_interface}.
Context {llci : leaderLogs_contiguous_interface}.
Context {ollpti : one_leaderLog_per_term_interface}.
Context {llsi : leaderLogs_sorted_interface}.
Context {tsi : term_sanity_interface}.
Context {rri : raft_refinement_interface}.
Context {aetsi : allEntries_term_sanity_interface}.
Definition no_entries_past_current_term_host_lifted net := forall (h : name) e, In e (log (snd (nwState net h))) -> eTerm e <= currentTerm (snd (nwState net h)).
Ltac inList x ls := match ls with | x => idtac | (_, x) => idtac | (?LS, _) => inList x LS end.
Ltac app f ls := match ls with | (?LS, ?X) => f X || app f LS || fail 1 | _ => f ls end.
Ltac all f ls := match ls with | (?LS, ?X) => f X; all f LS | (_, _) => fail 1 | _ => f ls end.
Instance aeli : allEntries_log_interface.
split.
eauto using allEntries_log_invariant.
Defined.
End AllEntriesLog.

Lemma term_ne_in_l2 : forall l e e' l1 l2, sorted l -> In e l -> (forall e', In e' l -> eTerm e' <= eTerm e) -> removeAfterIndex l (eIndex e) = l1 ++ l2 -> (forall e', In e' l1 -> eTerm e' = eTerm e) -> In e' l -> eTerm e' <> eTerm e -> In e' l2.
Proof using.
intros.
assert (eIndex e' <= eIndex e) by (eapply sorted_term_index_le; eauto; find_apply_hyp_hyp; destruct (lt_eq_lt_dec (eTerm e') (eTerm e)); intuition).
find_eapply_lem_hyp removeAfterIndex_le_In; eauto.
repeat find_rewrite.
do_in_app.
intuition.
find_apply_hyp_hyp.
intuition.
