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

Lemma votesWithLog_update_elections_data_request_vote : forall h st t src lli llt st' m t' h' l', handleRequestVote h (snd st) t src lli llt = (st', m) -> In (t', h', l') (votesWithLog (update_elections_data_requestVote h src t src lli llt st)) -> In (t', h', l') (votesWithLog (fst st)) \/ (t' = currentTerm st' /\ l' = log st').
Proof using.
unfold update_elections_data_requestVote.
intros.
repeat break_match; repeat tuple_inversion; intuition; simpl in *; intuition; tuple_inversion; intuition.
