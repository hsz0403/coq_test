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

Lemma update_elections_data_timeout_leaderLogs : forall h st, leaderLogs (update_elections_data_timeout h st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma update_elections_data_appendEntries_leaderLogs : forall h st t h' pli plt es ci, leaderLogs (update_elections_data_appendEntries h st t h' pli plt es ci) = leaderLogs (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
Admitted.

Lemma update_elections_data_requestVote_leaderLogs : forall h h' t lli llt st, leaderLogs (update_elections_data_requestVote h h' t h' lli llt st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_requestVote.
intros.
Admitted.

Lemma handleRequestVoteReply_spec : forall h st h' t v st', st' = handleRequestVoteReply h st h' t v -> log st' = log st /\ (currentTerm st' = currentTerm st \/ (currentTerm st <= currentTerm st' /\ type st' = Follower)).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
Admitted.

Lemma update_elections_data_requestVoteReply_leaderLogs : forall h h' t r st, leaderLogs (update_elections_data_requestVoteReply h h' t r st) = leaderLogs (fst st) \/ leaderLogs (update_elections_data_requestVoteReply h h' t r st) = (currentTerm (snd st), log (snd st)) :: leaderLogs (fst st).
Proof using.
intros.
unfold update_elections_data_requestVoteReply in *.
repeat break_match; intuition.
simpl in *.
match goal with | |- context [handleRequestVoteReply ?h ?s ?h' ?t ?r] => pose proof handleRequestVoteReply_spec h s h' t r (handleRequestVoteReply h s h' t r) end.
intuition; repeat find_rewrite; intuition.
Admitted.

Theorem lift_log_matching : forall net, refined_raft_intermediate_reachable net -> log_matching (deghost net).
Proof using lmi rri.
intros.
Admitted.

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
Admitted.

Lemma leaderLogs_contiguous_init : refined_raft_net_invariant_init leaderLogs_contiguous.
Proof using.
Admitted.

Lemma leaderLogs_contiguous_client_request : refined_raft_net_invariant_client_request leaderLogs_contiguous.
Proof using.
start.
find_rewrite_lem update_elections_data_client_request_leaderLogs.
Admitted.

Lemma leaderLogs_contiguous_timeout : refined_raft_net_invariant_timeout leaderLogs_contiguous.
Proof using.
start.
find_rewrite_lem update_elections_data_timeout_leaderLogs.
Admitted.

Lemma update_elections_data_client_request_leaderLogs : forall h st client id c, leaderLogs (update_elections_data_client_request h st client id c) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_client_request in *.
intros.
repeat break_match; repeat find_inversion; auto.
