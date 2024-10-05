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

Lemma appendEntries_haveNewEntries_false : forall net p t n pli plt es ci h e, refined_raft_intermediate_reachable net -> In p (nwPackets net) -> pBody p = AppendEntries t n pli plt es ci -> haveNewEntries (snd (nwState net h)) es = false -> In e es -> In e (log (snd (nwState net h))).
Proof using rlmli.
intros.
unfold haveNewEntries in *.
do_bool.
intuition; [unfold not_empty in *; break_match; subst; simpl in *; intuition; congruence|].
break_match; try congruence.
do_bool.
find_apply_lem_hyp findAtIndex_elim.
intuition.
assert (es <> nil) by (destruct es; subst; simpl in *; intuition; congruence).
find_eapply_lem_hyp maxIndex_non_empty.
break_exists.
intuition.
find_copy_eapply_lem_hyp entries_sorted_nw_invariant; eauto.
match goal with | H : In e es |- _ => copy_eapply maxIndex_is_max H; eauto end.
repeat find_rewrite.
find_eapply_lem_hyp entries_match_nw_host_invariant; eauto.
