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

Lemma handleRequestVoteReply_spec : forall h st h' t v st', st' = handleRequestVoteReply h st h' t v -> log st' = log st /\ (currentTerm st' = currentTerm st \/ (currentTerm st <= currentTerm st' /\ type st' = Follower)).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
repeat break_match; try find_inversion; subst; simpl in *; intuition; do_bool; intuition.
