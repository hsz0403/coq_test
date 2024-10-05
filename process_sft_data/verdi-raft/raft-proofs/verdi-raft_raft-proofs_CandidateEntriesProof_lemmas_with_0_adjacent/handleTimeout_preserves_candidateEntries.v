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

Lemma handleTimeout_preserves_candidateEntries : forall net h e out d l, refined_raft_intermediate_reachable net -> handleTimeout h (snd (nwState net h)) = (out, d, l) -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_timeout h (nwState net h), d)).
Proof using cti.
intros.
destruct (serverType_eq_dec (type (snd (A:=electionsData) (B:=raft_data) (nwState net h))) Leader).
+
unfold handleTimeout, tryToBecomeLeader in *.
simpl in *.
find_rewrite.
find_inversion.
eapply candidateEntries_same; eauto; intros; repeat (rewrite update_fun_comm; simpl in * ); update_destruct; subst; rewrite_update; auto using update_elections_data_timeout_leader_cronies_same.
+
unfold candidateEntries in *.
break_exists.
break_and.
exists x.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm; simpl.
rewrite update_fun_comm with (f := type); simpl.
update_destruct; subst; rewrite_update; auto.
split.
*
match goal with | [ H : handleTimeout _ _ = _ |- _ ] => pose proof H; apply update_elections_data_timeout_cronies with (t := eTerm e) in H end.
intuition; find_rewrite; auto.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
find_copy_apply_lem_hyp cronies_term_invariant; auto.
find_copy_apply_lem_hyp handleTimeout_not_leader_inc_term; auto.
simpl in *.
omega.
*
intros.
find_apply_lem_hyp wonElection_exists_voter.
break_exists.
find_apply_lem_hyp in_dedup_was_in.
find_copy_apply_lem_hyp cronies_term_invariant; auto.
find_copy_apply_lem_hyp handleTimeout_not_leader_inc_term; auto.
simpl in *.
omega.
