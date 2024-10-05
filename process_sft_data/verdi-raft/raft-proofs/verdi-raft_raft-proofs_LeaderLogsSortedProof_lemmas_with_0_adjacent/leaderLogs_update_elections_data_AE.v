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

Lemma leaderLogs_update_elections_data_AE : forall me st t li pli plt es lci, leaderLogs (update_elections_data_appendEntries me st t li pli plt es lci) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_appendEntries.
intros.
repeat break_match; subst; auto.
