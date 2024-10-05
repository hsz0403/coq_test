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

Lemma candidate_entries_do_generic_server : refined_raft_net_invariant_do_generic_server CandidateEntries.
Proof using.
red.
unfold CandidateEntries.
intros.
intuition; simpl in *.
-
unfold candidateEntries_host_invariant in *.
intros.
eapply candidateEntries_ext; eauto.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update.
+
simpl in *.
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
find_rewrite.
repeat match goal with | [ H : nwState ?net ?h = (_, ?d), H' : context [ log ?d ] |- _ ] => replace (log d) with (log (snd (nwState net h))) in H' by (repeat find_rewrite; auto) end.
eauto using doGenericServer_preserves_candidateEntries.
+
eauto using doGenericServer_preserves_candidateEntries.
-
unfold candidateEntries_nw_invariant in *.
intros.
simpl in *.
eapply candidateEntries_ext; eauto.
find_apply_hyp_hyp.
intuition.
+
eauto using doGenericServer_preserves_candidateEntries.
+
do_in_map.
find_copy_apply_lem_hyp doGenericServer_spec.
break_and.
subst.
simpl in *.
find_apply_hyp_hyp.
exfalso.
find_rewrite.
eauto 20.
