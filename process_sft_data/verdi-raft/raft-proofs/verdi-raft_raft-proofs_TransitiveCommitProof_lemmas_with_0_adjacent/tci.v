Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.LeaderCompletenessInterface.
Require Import VerdiRaft.RefinedLogMatchingLemmasInterface.
Require Import VerdiRaft.TransitiveCommitInterface.
Section TransitiveCommit.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {rlmli : refined_log_matching_lemmas_interface}.
Instance tci : transitive_commit_interface.
Proof.
split.
exact transitive_commit_invariant.
End TransitiveCommit.

Instance tci : transitive_commit_interface.
Proof.
split.
exact transitive_commit_invariant.
