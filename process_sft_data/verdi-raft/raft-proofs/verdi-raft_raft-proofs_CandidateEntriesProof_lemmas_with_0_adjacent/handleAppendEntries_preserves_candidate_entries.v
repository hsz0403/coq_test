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

Lemma handleAppendEntries_preserves_candidate_entries : forall net h t n pli plt es ci d m e, handleAppendEntries h (snd (nwState net h)) t n pli plt es ci = (d, m) -> refined_raft_intermediate_reachable net -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_appendEntries h (nwState net h) t n pli plt es ci, d)).
Proof using.
unfold candidateEntries.
intros.
break_exists.
break_and.
exists x.
split.
-
rewrite update_fun_comm.
simpl.
rewrite update_fun_comm.
simpl.
rewrite update_elections_data_appendEntries_cronies_same.
destruct (name_eq_dec x h); subst; rewrite_update; auto.
-
intros.
rewrite update_fun_comm.
simpl.
find_rewrite_lem update_fun_comm.
simpl in *.
destruct (name_eq_dec x h); subst; rewrite_update; auto.
find_apply_lem_hyp handleAppendEntries_term_same_or_type_follower.
intro; intuition; repeat find_rewrite; auto; discriminate.
