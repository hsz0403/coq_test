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

Lemma votesWithLog_update_elections_data_timeout : forall h st out st' ps t' h' l', handleTimeout h (snd st) = (out, st', ps) -> In (t', h', l') (votesWithLog (update_elections_data_timeout h st)) -> In (t', h', l') (votesWithLog (fst st)) \/ (t' = currentTerm st' /\ l' = log st').
Proof using.
unfold update_elections_data_timeout.
intros.
repeat break_match; simpl in *; intuition; repeat tuple_inversion; intuition.
