Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CandidatesVoteForSelvesInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Section CroniesCorrectProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {vci : votes_correct_interface}.
Context {cvfsi : candidates_vote_for_selves_interface}.
Instance cci : cronies_correct_interface.
Proof.
split.
auto using cronies_correct_invariant.
End CroniesCorrectProof.

Lemma update_elections_data_requestVote_votedFor : forall h h' t lli llt st st' m, handleRequestVote h (snd st) t h' lli llt = (st', m) -> votedFor st' = Some h' -> In (currentTerm st', h') (votes (update_elections_data_requestVote h h' t h' lli llt st)) \/ (votedFor st' = votedFor (snd st) /\ currentTerm st' = currentTerm (snd st)).
Proof using.
intros.
unfold update_elections_data_requestVote in *.
repeat break_match; simpl in *; repeat (repeat find_inversion; repeat find_rewrite); repeat (do_bool; break_and); try congruence; intuition.
