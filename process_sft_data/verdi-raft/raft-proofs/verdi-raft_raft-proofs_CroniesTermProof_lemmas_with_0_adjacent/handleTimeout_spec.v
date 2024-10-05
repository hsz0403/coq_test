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

Lemma handleTimeout_spec : forall h st out st' l t h', handleTimeout h (snd st) = (out, st', l) -> In h' (cronies (update_elections_data_timeout h st) t) -> (currentTerm (snd st) <= currentTerm st' /\ (In h' (cronies (fst st) t) \/ t = currentTerm st')).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader, update_elections_data_timeout in *.
repeat (break_match; repeat find_inversion; simpl in *; auto); intuition; unfold handleTimeout, tryToBecomeLeader in *; repeat (break_match; repeat find_inversion; simpl in *; auto); congruence.
