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

Lemma leaderLogs_update_elections_data_RVR : forall h src t1 v st t2 ll st', handleRequestVoteReply h (snd st) src t1 v = st' -> In (t2, ll) (leaderLogs (update_elections_data_requestVoteReply h src t1 v st)) -> In (t2, ll) (leaderLogs (fst st)) \/ (type st' = Leader /\ type (snd st) = Candidate /\ t2 = currentTerm st' /\ ll = log st').
Proof using.
unfold update_elections_data_requestVoteReply.
intros.
repeat break_match; repeat find_inversion; intuition.
simpl in *.
intuition.
find_inversion.
intuition.
