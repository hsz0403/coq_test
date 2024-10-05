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

Lemma handleRequestVoteReply_spec : forall h st h' t v st', st' = handleRequestVoteReply h st h' t v -> currentTerm st' = currentTerm st \/ (currentTerm st <= currentTerm st' /\ type st' = Follower).
Proof using.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
repeat break_match; try find_inversion; subst; simpl in *; intuition; do_bool; intuition.
