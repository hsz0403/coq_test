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

Lemma handleTimeout_rvr : forall h net ps out d l p t v, handleTimeout h (snd (nwState net h)) = (out, d, l) -> (forall p' : packet, In p' ps -> In p' (nwPackets net) \/ In p' (send_packets h l)) -> pBody p = RequestVoteReply t v -> In p ps -> In p (nwPackets net).
Proof using.
intros.
unfold handleTimeout, tryToBecomeLeader in *; repeat break_match; repeat find_inversion; subst; simpl in *; find_apply_hyp_hyp; in_crush; congruence.
