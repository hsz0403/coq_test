Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CroniesTermInterface.
Section CroniesTermProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Instance cti : cronies_term_interface.
Proof.
split.
auto using cronies_term_invariant.
End CroniesTermProof.

Lemma handleAppendEntriesReply_spec : forall h st h' t es r st' ms, handleAppendEntriesReply h st h' t es r = (st', ms) -> currentTerm st <= currentTerm st'.
Proof using.
intros.
unfold handleAppendEntriesReply, advanceCurrentTerm in *.
repeat break_match; try find_inversion; subst; simpl in *; do_bool; intuition.
