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

Lemma wonElection_candidateEntries_rvr : forall (net : network (params := raft_refined_multi_params)) p e, votes_correct net -> cronies_correct net -> candidateEntries e (nwState net) -> In p (nwPackets net) -> pBody p = RequestVoteReply (eTerm e) true -> currentTerm (snd (nwState net (pDst p))) = eTerm e -> wonElection (dedup name_eq_dec (pSrc p :: votesReceived (snd (nwState net (pDst p))))) = true -> type (snd (nwState net (pDst p))) <> Candidate.
Proof using.
unfold votes_correct, cronies_correct.
intros.
break_and.
match goal with | [ H : context [ votes_nw ], H' : context [ pBody ] |- _ ] => eapply H in H' end.
unfold candidateEntries in *.
break_exists.
break_and.
match goal with | H : wonElection _ = _ |- _ => eapply wonElection_one_in_common in H; [|clear H; eauto] end.
break_exists.
break_and.
simpl in *.
intuition.
-
subst.
apply_prop_hyp cronies_votes In.
assert (x = pDst p) by (eapply_prop one_vote_per_term; eauto).
subst.
concludes.
contradiction.
-
apply_prop_hyp votes_received_cronies In.
concludes.
apply_prop_hyp cronies_votes In.
apply_prop_hyp cronies_votes In.
unfold raft_data in *.
unfold raft_refined_base_params, raft_refined_multi_params in *.
simpl in *.
repeat find_reverse_rewrite.
assert (x = pDst p) by (eapply_prop one_vote_per_term; eauto).
subst.
repeat concludes.
contradiction.
