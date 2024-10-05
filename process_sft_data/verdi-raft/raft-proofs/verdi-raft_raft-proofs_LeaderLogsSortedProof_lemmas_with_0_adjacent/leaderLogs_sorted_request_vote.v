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
eauto.
