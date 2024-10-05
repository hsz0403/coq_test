Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.AppendEntriesRequestTermSanityInterface.
Section AppendEntriesRequestTermSanity.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {si : sorted_interface}.
Instance aertsi : append_entries_request_term_sanity_interface.
Proof.
split.
intros.
find_apply_lem_hyp lift_sorted.
eauto using logs_sorted_aerts.
End AppendEntriesRequestTermSanity.

Lemma logs_sorted_aerts : forall net, logs_sorted (deghost net) -> append_entries_request_term_sanity net.
Proof using.
unfold logs_sorted, append_entries_request_term_sanity.
intuition.
unfold packets_ge_prevTerm in *.
find_apply_lem_hyp ghost_packet.
eauto.
