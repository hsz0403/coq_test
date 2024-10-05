Require Import VerdiRaft.Raft.
Require Import VerdiRaft.SortedInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.UniqueIndicesInterface.
Section UniqueIndices.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {si : sorted_interface}.
Instance uii : unique_indices_interface.
Proof.
split.
exact UniqueIndices_invariant.
End UniqueIndices.

Instance uii : unique_indices_interface.
Proof.
split.
exact UniqueIndices_invariant.
