Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Section SpecLemmas.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
End SpecLemmas.

Lemma votesWithLog_same_append_entries : forall h st t n pli plt es ci, votesWithLog (update_elections_data_appendEntries h st t n pli plt es ci) = votesWithLog (fst st).
Proof using.
intros.
unfold update_elections_data_appendEntries.
repeat break_match; auto.
