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

Lemma update_elections_data_timeout_cronies : forall h st t, cronies (update_elections_data_timeout h st) t = cronies (fst st) t \/ (cronies (update_elections_data_timeout h st) t = [h] /\ t = S (currentTerm (snd st))).
Proof using.
intros.
unfold update_elections_data_timeout.
repeat break_match; simpl; auto.
unfold handleTimeout, tryToBecomeLeader in *.
repeat break_match; find_inversion; simpl in *; auto; congruence.
