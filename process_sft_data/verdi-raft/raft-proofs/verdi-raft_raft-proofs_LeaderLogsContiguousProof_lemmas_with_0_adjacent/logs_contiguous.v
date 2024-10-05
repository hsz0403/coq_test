Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.LeaderLogsContiguousInterface.
Require Import VerdiRaft.LogMatchingInterface.
Section LeaderLogsContiguous.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {lmi : log_matching_interface}.
Ltac start := red; unfold leaderLogs_contiguous; intros; subst; simpl in *; find_higher_order_rewrite; update_destruct; subst; rewrite_update; eauto; simpl in *.
Instance llci : leaderLogs_contiguous_interface : Prop.
Proof.
split.
exact leaderLogs_contiguous_invariant.
End LeaderLogsContiguous.

Theorem logs_contiguous : forall net h, refined_raft_intermediate_reachable net -> contiguous_range_exact_lo (log (snd (nwState net h))) 0.
Proof using lmi rri.
intros.
find_apply_lem_hyp lift_log_matching.
unfold log_matching, log_matching_hosts in *.
intuition.
split.
-
intros.
match goal with | H : forall _ _, _ <= _ <= _ -> _ |- _ => specialize (H h i); conclude H ltac:(simpl; repeat break_match; simpl in *; repeat find_rewrite; simpl in *;omega) end.
break_exists_exists; intuition.
simpl in *.
repeat break_match; simpl in *; repeat find_rewrite; simpl in *; auto.
-
intros.
cut (eIndex e > 0); intros; try omega.
cut (In e (log (nwState (deghost net) h))); intros; eauto.
simpl in *.
repeat break_match.
simpl in *.
repeat find_rewrite.
simpl in *.
auto.
