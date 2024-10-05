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

Lemma leaderLogs_contiguous_append_entries : refined_raft_net_invariant_append_entries leaderLogs_contiguous.
Proof using.
start.
find_rewrite_lem update_elections_data_appendEntries_leaderLogs.
Admitted.

Lemma leaderLogs_contiguous_append_entries_reply : refined_raft_net_invariant_append_entries_reply leaderLogs_contiguous.
Proof using.
Admitted.

Lemma leaderLogs_contiguous_request_vote : refined_raft_net_invariant_request_vote leaderLogs_contiguous.
Proof using.
start.
find_rewrite_lem update_elections_data_requestVote_leaderLogs.
Admitted.

Lemma leaderLogs_contiguous_request_vote_reply : refined_raft_net_invariant_request_vote_reply leaderLogs_contiguous.
Proof using lmi rri.
start.
match goal with | [ _ : context [ update_elections_data_requestVoteReply ?d ?s ?t ?v ?st ] |- _ ] => pose proof update_elections_data_requestVoteReply_leaderLogs d s t v st end.
intuition; repeat find_rewrite; eauto.
simpl in *; break_or_hyp; eauto.
find_inversion.
Admitted.

Lemma leaderLogs_contiguous_do_leader : refined_raft_net_invariant_do_leader leaderLogs_contiguous.
Proof using.
start.
replace gd with (fst (nwState net h0)) in *; eauto.
Admitted.

Lemma leaderLogs_contiguous_do_generic_server : refined_raft_net_invariant_do_generic_server leaderLogs_contiguous.
Proof using.
start.
replace gd with (fst (nwState net h0)) in *; eauto.
Admitted.

Lemma leaderLogs_contiguous_state_same_packet_subset : refined_raft_net_invariant_state_same_packet_subset leaderLogs_contiguous.
Proof using.
red.
unfold leaderLogs_contiguous.
intros.
find_reverse_higher_order_rewrite.
Admitted.

Lemma leaderLogs_contiguous_reboot : refined_raft_net_invariant_reboot leaderLogs_contiguous.
Proof using.
start.
replace gd with (fst (nwState net h0)) in *; eauto.
Admitted.

Instance llci : leaderLogs_contiguous_interface : Prop.
Proof.
split.
Admitted.

Lemma leaderLogs_contiguous_invariant : forall net, refined_raft_intermediate_reachable net -> leaderLogs_contiguous net.
Proof using lmi rri.
intros.
apply refined_raft_net_invariant; auto.
-
apply leaderLogs_contiguous_init.
-
apply leaderLogs_contiguous_client_request.
-
apply leaderLogs_contiguous_timeout.
-
apply leaderLogs_contiguous_append_entries.
-
apply leaderLogs_contiguous_append_entries_reply.
-
apply leaderLogs_contiguous_request_vote.
-
apply leaderLogs_contiguous_request_vote_reply.
-
apply leaderLogs_contiguous_do_leader.
-
apply leaderLogs_contiguous_do_generic_server.
-
apply leaderLogs_contiguous_state_same_packet_subset.
-
apply leaderLogs_contiguous_reboot.
