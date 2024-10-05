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

Lemma leaderLogs_contiguous_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_contiguous.
Proof using lmi rri.
start.
match goal with | [ _ : context [ update_elections_data_requestVoteReply ?d ?s ?t ?v ?st ] |- _ ] => pose proof update_elections_data_requestVoteReply_leaderLogs d s t v st end.
intuition; repeat find_rewrite; eauto.
simpl in *; break_or_hyp; eauto.
find_inversion.
eauto using logs_contiguous.
