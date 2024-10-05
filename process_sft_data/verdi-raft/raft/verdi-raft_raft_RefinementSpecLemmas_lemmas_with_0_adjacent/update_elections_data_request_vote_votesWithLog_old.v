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

Lemma update_elections_data_request_vote_votesWithLog_old : forall (h : name) (st : electionsData * RaftState.raft_data term name entry logIndex serverType data clientId output) (t : nat) (src : fin N) (lli llt : nat) (t' : term) (h' : name) (l' : list entry), In (t', h', l') (votesWithLog (fst st)) -> In (t', h', l') (votesWithLog (update_elections_data_requestVote h src t src lli llt st)).
Proof using.
intros.
unfold update_elections_data_requestVote in *.
repeat break_match; simpl in *; intuition.
