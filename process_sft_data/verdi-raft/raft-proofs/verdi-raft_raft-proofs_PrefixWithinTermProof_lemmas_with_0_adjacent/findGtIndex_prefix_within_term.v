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

Lemma findGtIndex_prefix_within_term : forall l1 l2 i, prefix_within_term l1 l2 -> prefix_within_term (findGtIndex l1 i) l2.
Proof using.
unfold prefix_within_term.
intros.
find_apply_lem_hyp findGtIndex_in.
eauto.
