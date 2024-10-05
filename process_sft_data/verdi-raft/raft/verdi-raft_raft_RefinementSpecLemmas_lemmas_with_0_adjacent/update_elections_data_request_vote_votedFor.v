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

Lemma update_elections_data_request_vote_votedFor : forall h h' cid t lli llt st st' m, handleRequestVote h (snd st) t h' lli llt = (st', m) -> votedFor st' = Some cid -> (votedFor (snd st) = Some cid /\ currentTerm st' = currentTerm (snd st)) \/ (cid = h' /\ currentTerm st' = t /\ votesWithLog (update_elections_data_requestVote h h' t h' lli llt st) = (currentTerm st', cid, (log st')) :: votesWithLog (fst st) /\ moreUpToDate llt lli (maxTerm (log st')) (maxIndex (log st')) = true).
Proof using.
intros.
unfold update_elections_data_requestVote.
repeat find_rewrite.
unfold handleRequestVote, advanceCurrentTerm in *.
repeat break_match; repeat find_inversion; simpl in *; auto; try congruence; find_inversion; auto; do_bool; intuition; try congruence.
do_bool.
subst.
intuition.
