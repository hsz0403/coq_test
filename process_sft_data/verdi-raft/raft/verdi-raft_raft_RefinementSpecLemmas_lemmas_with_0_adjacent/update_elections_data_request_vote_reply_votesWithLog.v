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

Lemma update_elections_data_request_vote_reply_votesWithLog : forall (h : name) (st : electionsData * RaftState.raft_data term name entry logIndex serverType data clientId output) (src : name) (t : nat) (r : bool), votesWithLog (update_elections_data_requestVoteReply h src t r st) = votesWithLog (fst st).
Proof using.
intros.
unfold update_elections_data_requestVoteReply.
break_match; simpl in *; auto.
