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

Lemma do_generic_server_pkts : forall h st os st' ms ps ps' p t v, doGenericServer h st = (os, st', ms) -> (forall p, In p ps' -> In p ps \/ In p (send_packets h ms)) -> pBody p = RequestVoteReply t v -> In p ps' -> In p ps.
Proof using.
intros.
find_apply_hyp_hyp.
intuition.
unfold doGenericServer in *.
repeat break_match; find_inversion; simpl in *; intuition.
