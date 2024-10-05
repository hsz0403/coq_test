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

Lemma update_elections_data_client_request_leaderLogs : forall h st client id c, leaderLogs (update_elections_data_client_request h st client id c) = leaderLogs (fst st).
Proof using.
unfold update_elections_data_client_request in *.
intros.
repeat break_match; repeat find_inversion; auto.
