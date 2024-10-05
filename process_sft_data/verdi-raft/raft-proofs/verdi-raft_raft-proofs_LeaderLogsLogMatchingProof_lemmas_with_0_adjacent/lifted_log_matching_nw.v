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

Lemma lifted_log_matching_nw : forall net, refined_raft_intermediate_reachable net -> forall p t leaderId prevLogIndex prevLogTerm entries leaderCommit, In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> (forall h e1 e2, In e1 entries -> In e2 (log (snd (nwState net h))) -> eIndex e1 = eIndex e2 -> eTerm e1 = eTerm e2 -> (forall e3, eIndex e3 <= eIndex e1 -> In e3 entries -> In e3 (log (snd (nwState net h)))) /\ (prevLogIndex <> 0 -> exists e4, eIndex e4 = prevLogIndex /\ eTerm e4 = prevLogTerm /\ In e4 (log (snd (nwState net h))))) /\ (forall i, prevLogIndex < i <= maxIndex entries -> exists e, eIndex e = i /\ In e entries) /\ (forall e, In e entries -> prevLogIndex < eIndex e).
Proof using lmi rri.
intros.
find_apply_lem_hyp lifted_log_matching.
unfold log_matching, log_matching_nw in *.
break_and.
match goal with | [ H : forall _ : packet , _ |- _ ] => do 7 insterU H; conclude H ltac:(unfold deghost; simpl; eapply in_map_iff; eexists; eauto); conclude H ltac:(simpl; eauto) end.
intuition.
-
rewrite <- deghost_spec with (net0 := net).
eapply H3 with (e1:=e1)(e2:=e2); eauto.
rewrite deghost_spec.
auto.
-
rewrite <- deghost_spec with (net0 := net).
eapply H3 with (e1:=e1)(e2:=e2); eauto.
rewrite deghost_spec.
auto.
