Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.AllEntriesLeaderSublogInterface.
Require Import VerdiRaft.LeaderSublogInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.AllEntriesLogMatchingInterface.
Section AllEntriesLogMatching.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {aelsi : allEntries_leader_sublog_interface}.
Context {lsi : leader_sublog_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Definition allEntries_log_matching_nw net := forall (e e' : entry) (h : name) (p : packet) t leaderId prevLogIndex prevLogTerm entries leaderCommit, In p (nwPackets net) -> pBody p = AppendEntries t leaderId prevLogIndex prevLogTerm entries leaderCommit -> In e entries -> In e' (map snd (allEntries (fst (nwState net h)))) -> eTerm e = eTerm e' -> eIndex e = eIndex e' -> e = e'.
Definition allEntries_log_matching_inductive net := allEntries_log_matching net /\ allEntries_log_matching_nw net.
Ltac start := red; unfold allEntries_log_matching_inductive; simpl; intros.
Ltac start_update := start; intuition; [unfold allEntries_log_matching in *|unfold allEntries_log_matching_nw in *]; intros; repeat find_higher_order_rewrite; repeat (update_destruct; rewrite_update); subst; simpl; eauto.
Definition leader_sublog (net : network) := forall leader e h, type (snd (nwState net leader)) = Leader -> In e (log (snd (nwState net h))) -> eTerm e = currentTerm (snd (nwState net leader)) -> In e (log (snd (nwState net leader))).
Ltac fix_data := do 2 (unfold raft_data in *; simpl in *).
Ltac contradict_maxIndex := exfalso; find_apply_lem_hyp maxIndex_is_max; try (fix_data; omega); eapply entries_sorted_invariant; eauto.
Ltac unchanged := red; intros; eapply allEntries_log_matching_unchanged; subst; eauto.
Instance aelmi : allEntries_log_matching_interface.
Proof.
constructor.
intros.
apply allEntries_log_matching_inductive_invariant; auto.
End AllEntriesLogMatching.

Lemma lifted_leader_sublog_invariant : forall net, refined_raft_intermediate_reachable net -> leader_sublog net.
Proof using lsi rri.
pose proof lift_prop _ leader_sublog_invariant_invariant.
unfold leader_sublog, leader_sublog_invariant, leader_sublog_host_invariant in *.
intuition.
unfold raft_refined_base_params in *.
repeat rewrite <- deghost_spec in *.
repeat match goal with | [ H : _ |- _ ] => rewrite <- deghost_spec in H end.
find_apply_hyp_hyp.
intuition.
eauto.
