Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.OneLeaderPerTermInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.LeaderSublogInterface.
Hint Extern 4 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 4 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 4 (@FailureParams _ _) => apply failure_params : typeclass_instances.
Section LeaderSublogProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Context {olpti : one_leader_per_term_interface}.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Notation is_append_entries m := (exists t n prevT prevI entries c, m = AppendEntries t n prevT prevI entries c).
Definition CandidateEntriesLowered net e h := currentTerm (nwState net h) = eTerm e -> wonElection (dedup name_eq_dec (votesReceived (nwState net h))) = true -> type (nwState net h) <> Candidate.
Definition CandidateEntriesLowered_rvr net e p := In p (nwPackets net) -> pBody p = RequestVoteReply (eTerm e) true -> currentTerm (nwState net (pDst p)) = eTerm e -> wonElection (dedup name_eq_dec (pSrc p :: votesReceived (nwState net (pDst p)))) = true -> type (nwState net (pDst p)) <> Candidate.
Instance lsi : leader_sublog_interface.
Proof.
split.
auto using leader_sublog_invariant_invariant.
End LeaderSublogProof.

Lemma candidate_entries_lowered_nw' : forall net, CandidateEntries net -> votes_correct net -> cronies_correct net -> forall h p e t li pli plt es lc, pBody p = AppendEntries t li pli plt es lc -> In p (nwPackets (deghost net)) -> In e es -> CandidateEntriesLowered (deghost net) e h.
Proof using rri.
unfold CandidateEntriesLowered, CandidateEntries, votes_correct, cronies_correct.
intros.
break_and.
rewrite deghost_spec.
find_apply_lem_hyp deghost_packet_exists.
break_exists.
break_and.
subst.
eapply_prop_hyp candidateEntries_nw_invariant In; eauto.
unfold candidateEntries in *.
break_exists.
break_and.
match goal with | H : wonElection _ = _ |- _ => eapply wonElection_one_in_common in H; [|clear H; eauto] end.
break_exists.
break_and.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
intro.
assert (h = x0).
{
eapply_prop one_vote_per_term; eapply_prop cronies_votes.
-
eapply_prop votes_received_cronies; eauto.
-
find_reverse_rewrite.
auto.
}
subst.
concludes.
contradiction.
