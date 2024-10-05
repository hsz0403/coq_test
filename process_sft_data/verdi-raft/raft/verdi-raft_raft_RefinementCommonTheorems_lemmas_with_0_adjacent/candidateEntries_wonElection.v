Require Import Verdi.GhostSimulations.
Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CommonTheorems.
Require Export VerdiRaft.RefinementCommonDefinitions.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Section CommonTheorems.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {cci : cronies_correct_interface}.
Context {vci : votes_correct_interface}.
End CommonTheorems.
Ltac intro_refined_invariant lem := match goal with | [ h: refined_raft_intermediate_reachable _ |- _ ] => let x := fresh in pose proof h as x; apply lem in x; unfold_invariant x end.

Lemma candidateEntries_wonElection : forall (net : network (params := raft_refined_multi_params)) e h, one_vote_per_term net -> cronies_votes net -> votes_received_cronies net -> candidateEntries e (nwState net) -> currentTerm (snd (nwState net h)) = eTerm e -> wonElection (dedup name_eq_dec (votesReceived (snd (nwState net h)))) = true -> type (snd (nwState net h)) <> Candidate.
Proof using.
intros.
unfold candidateEntries in *.
break_exists.
break_and.
repeat match goal with | [ H : _ |- _ ] => rewrite deghost_spec in H end.
intro.
assert (x = h).
{
match goal with | H : wonElection _ = _ |- _ => eapply wonElection_one_in_common in H; [|clear H; eauto] end.
break_exists.
break_and.
eapply_prop one_vote_per_term; try solve [eapply_prop cronies_votes; eauto].
eapply_prop cronies_votes.
repeat find_reverse_rewrite.
eapply_prop votes_received_cronies; auto.
}
subst.
concludes.
contradiction.
