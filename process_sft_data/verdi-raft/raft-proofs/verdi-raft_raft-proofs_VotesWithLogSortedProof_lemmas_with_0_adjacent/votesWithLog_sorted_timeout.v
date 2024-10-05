Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesWithLogSortedInterface.
Require Import VerdiRaft.SortedInterface.
Section VotesWithLogSorted.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance vwlsi : votesWithLog_sorted_interface.
Proof.
split.
exact votesWithLog_sorted_invariant.
End VotesWithLogSorted.

Lemma votesWithLog_sorted_timeout : refined_raft_net_invariant_timeout votesWithLog_sorted.
Proof using si rri.
unfold refined_raft_net_invariant_timeout, votesWithLog_sorted.
intros.
subst.
simpl in *.
find_higher_order_rewrite.
update_destruct_simplify; simpl in *.
-
destruct (votesWithLog (update_elections_data_timeout h0 (nwState net h0))) using (votesWithLog_update_elections_data_timeout ltac:(eauto)).
+
simpl in *.
intuition.
*
find_inversion.
erewrite handleTimeout_log_same by eauto.
eauto using sorted_host_lifted.
*
eauto.
+
eauto.
-
eauto.
