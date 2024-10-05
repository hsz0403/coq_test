Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.LeaderLogsSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section LeaderLogsSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance llsi : leaderLogs_sorted_interface.
Proof.
split.
eauto using leaderLogs_sorted_invariant.
Defined.
End LeaderLogsSorted.

Lemma leaderLogs_update_elections_data_client_request : forall me st client id c, leaderLogs (update_elections_data_client_request me st client id c) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_client_request.
intros.
Admitted.

Lemma leaderLogs_sorted_client_request : refined_raft_net_invariant_client_request leaderLogs_sorted.
Proof using.
unfold refined_raft_net_invariant_client_request, leaderLogs_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify; simpl in *.
-
rewrite leaderLogs_update_elections_data_client_request in *.
eauto.
-
Admitted.

Lemma sorted_host_lifted : forall net h, refined_raft_intermediate_reachable net -> sorted (log (snd (nwState net h))).
Proof using si rri.
intros.
pose proof (lift_prop _ logs_sorted_invariant).
find_insterU.
conclude_using eauto.
unfold logs_sorted, logs_sorted_host in *.
break_and.
unfold deghost in *.
simpl in *.
break_match.
Admitted.

Lemma leaderLogs_update_elections_data_timeout : forall h st, leaderLogs (update_elections_data_timeout h st) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_timeout.
intros.
Admitted.

Lemma leaderLogs_sorted_timeout : refined_raft_net_invariant_timeout leaderLogs_sorted.
Proof using.
unfold refined_raft_net_invariant_timeout, leaderLogs_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
Admitted.

Lemma leaderLogs_update_elections_data_AE : forall me st t li pli plt es lci, leaderLogs (update_elections_data_appendEntries me st t li pli plt es lci) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_appendEntries.
intros.
Admitted.

Lemma leaderLogs_sorted_append_entries : refined_raft_net_invariant_append_entries leaderLogs_sorted.
Proof using.
unfold refined_raft_net_invariant_append_entries, leaderLogs_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify; simpl in *.
-
rewrite leaderLogs_update_elections_data_AE in *.
eauto.
-
Admitted.

Lemma leaderLogs_sorted_append_entries_reply : refined_raft_net_invariant_append_entries_reply leaderLogs_sorted.
Proof using.
unfold refined_raft_net_invariant_append_entries_reply, leaderLogs_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
Admitted.

Lemma leaderLogs_sorted_request_vote : refined_raft_net_invariant_request_vote leaderLogs_sorted.
Proof using.
unfold refined_raft_net_invariant_request_vote, leaderLogs_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify.
-
unfold update_elections_data_requestVote in *.
repeat break_match; simpl in *; intuition; repeat find_inversion; eauto.
-
Admitted.

Lemma leaderLogs_update_elections_data_request_vote_reply : forall {h st h' t r st'}, handleRequestVoteReply h (snd st) h' t r = st' -> forall (P : list (term * list entry) -> Prop), (forall t, P ((t, log (snd st)) :: leaderLogs (fst st))) -> (P (leaderLogs (fst st))) -> (P (leaderLogs (update_elections_data_requestVoteReply h h' t r st))).
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; simpl in *; eauto.
repeat find_rewrite.
match goal with | H : handleRequestVoteReply _ _ _ _ _ = _ |- _ => symmetry in H end.
find_apply_lem_hyp handleRequestVoteReply_spec.
Admitted.

Lemma leaderLogs_sorted_init : refined_raft_net_invariant_init leaderLogs_sorted.
Proof using.
unfold refined_raft_net_invariant_init, leaderLogs_sorted.
intros.
subst.
simpl in *.
intuition.
