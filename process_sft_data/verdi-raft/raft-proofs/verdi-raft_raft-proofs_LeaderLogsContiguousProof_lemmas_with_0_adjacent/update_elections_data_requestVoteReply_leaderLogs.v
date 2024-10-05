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

Lemma update_elections_data_requestVoteReply_leaderLogs : forall h h' t r st, leaderLogs (update_elections_data_requestVoteReply h h' t r st) = leaderLogs (fst st) \/ leaderLogs (update_elections_data_requestVoteReply h h' t r st) = (currentTerm (snd st), log (snd st)) :: leaderLogs (fst st).
Proof using.
intros.
unfold update_elections_data_requestVoteReply in *.
repeat break_match; intuition.
simpl in *.
match goal with | |- context [handleRequestVoteReply ?h ?s ?h' ?t ?r] => pose proof handleRequestVoteReply_spec h s h' t r (handleRequestVoteReply h s h' t r) end.
intuition; repeat find_rewrite; intuition.
congruence.
