Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.VotesCorrectInterface.
Require Import VerdiRaft.TermSanityInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.RefinementCommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CandidateEntriesInterface.
Section CandidateEntriesProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cti : cronies_term_interface}.
Context {tsi : term_sanity_interface}.
Context {vci : votes_correct_interface}.
Context {cci : cronies_correct_interface}.
Ltac prove_in := match goal with | [ _ : nwPackets ?net = _, _ : In (?p : packet) _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; do_in_app; intuition) | [ _ : nwPackets ?net = _, _ : pBody ?p = _ |- _] => assert (In p (nwPackets net)) by (repeat find_rewrite; intuition) end.
Instance cei : candidate_entries_interface.
Proof.
split.
auto using candidate_entries_invariant.
End CandidateEntriesProof.

Lemma handleRV_advanceCurrentTerm_preserves_candidateEntries : forall net h h' t lli llt e, candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_requestVote h h' t h' lli llt (nwState net h), advanceCurrentTerm (snd (nwState net h)) t)).
Proof using.
intros.
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
split; update_destruct; subst; rewrite_update; auto; simpl.
+
rewrite update_elections_data_requestVote_cronies_same.
auto.
+
intros.
match goal with | [ |- context [advanceCurrentTerm ?st ?t] ] => pose proof advanceCurrentTerm_same_or_type_follower st t end.
intuition; try congruence.
repeat find_rewrite.
auto.
