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

Lemma ghost_packet : forall (net : network (params := raft_refined_multi_params)) p, In p (nwPackets net) -> In (deghost_packet p) (nwPackets (deghost net)).
Proof using.
unfold deghost.
simpl.
intuition.
apply in_map_iff.
eexists; eauto.
