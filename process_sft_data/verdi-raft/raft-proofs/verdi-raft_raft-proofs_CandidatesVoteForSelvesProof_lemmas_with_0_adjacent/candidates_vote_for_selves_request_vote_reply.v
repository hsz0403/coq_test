Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Section CandidatesVoteForSelvesProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Ltac rewrite_state := match goal with | [st : name -> raft_data, H : forall _, ?st _ = _ |- _] => rewrite H in * end.
Ltac t := repeat break_match; simpl in *; try find_inversion; rewrite_state; try use_applyEntries_spec; repeat break_if; subst; eauto; simpl in *; try discriminate.
Instance cvfsi : candidates_vote_for_selves_interface.
Proof.
split.
exact candidates_vote_for_selves_invariant.
End CandidatesVoteForSelvesProof.

Lemma candidates_vote_for_selves_request_vote_reply : raft_net_invariant_request_vote_reply candidates_vote_for_selves.
Proof using.
unfold raft_net_invariant_request_vote_reply, candidates_vote_for_selves.
intros.
unfold handleRequestVoteReply, advanceCurrentTerm in *.
t.
