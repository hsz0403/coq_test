Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeadersHaveLeaderLogsStrongInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.LogMatchingInterface.
Require Import VerdiRaft.AppendEntriesRequestLeaderLogsInterface.
Require Import VerdiRaft.NextIndexSafetyInterface.
Section AppendEntriesRequestLeaderLogs.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {lhllsi : leaders_have_leaderLogs_strong_interface}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Context {lmi : log_matching_interface}.
Context {nisi : nextIndex_safety_interface}.
Ltac start := red; unfold append_entries_leaderLogs; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance aerlli : append_entries_leaderLogs_interface.
split.
exact append_entries_leaderLogs_invariant.
End AppendEntriesRequestLeaderLogs.

Lemma nextIndex_sanity : forall net h h', refined_raft_intermediate_reachable net -> type (snd (nwState net h)) = Leader -> pred (getNextIndex (snd (nwState net h)) h') <> 0 -> exists e, findAtIndex (log (snd (nwState net h))) (pred (getNextIndex (snd (nwState net h)) h')) = Some e.
Proof using nisi lmi si rri.
intros.
find_copy_apply_lem_hyp lift_log_matching.
find_copy_apply_lem_hyp lift_nextIndex_safety.
assert (pred (getNextIndex (snd (nwState net h)) h') > 0) by omega.
unfold log_matching, log_matching_hosts in *.
unfold nextIndex_safety in *.
match goal with | H : forall _ _, type _ = _ -> _ |- _ => specialize (H h h') end.
intuition.
match goal with | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h (pred (getNextIndex (snd (nwState net h)) h'))) end.
unfold raft_refined_base_params in *.
repeat find_rewrite_lem deghost_spec.
intuition.
break_exists_exists.
intuition.
apply findAtIndex_intro; eauto using lift_logs_sorted, sorted_uniqueIndices.
