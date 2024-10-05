Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CroniesTermInterface.
Require Import VerdiRaft.CroniesCorrectInterface.
Require Import VerdiRaft.CandidateEntriesInterface.
Require Import VerdiRaft.RefinementSpecLemmas.
Require Import VerdiRaft.RefinementCommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.PrevLogCandidateEntriesTermInterface.
Section PrevLogCandidateEntriesTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Context {cei : candidate_entries_interface}.
Context {cti : cronies_term_interface}.
Context {cci : cronies_correct_interface}.
Instance plceti : prevLog_candidateEntriesTerm_interface.
Proof.
constructor.
apply prevLog_candidateEntriesTerm_invariant.
End PrevLogCandidateEntriesTerm.

Lemma handleRequestVoteReply_preserves_candidateEntriesTerm : forall net h h' t r st' t', handleRequestVoteReply h (snd (nwState net h)) h' t r = st' -> refined_raft_intermediate_reachable net -> candidateEntriesTerm t' (nwState net) -> candidateEntriesTerm t' (update name_eq_dec (nwState net) h (update_elections_data_requestVoteReply h h' t r (nwState net h), st')).
Proof using cci.
unfold candidateEntriesTerm.
intros.
break_exists_exists.
update_destruct_simplify; auto.
break_and.
unfold raft_data in *.
simpl in *.
unfold update_elections_data_requestVoteReply.
match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] => remember (handleRequestVoteReply h st h' t r) as new_state end; find_copy_apply_lem_hyp handleRequestVoteReply_spec.
repeat (break_match); intuition; repeat find_rewrite; intuition; simpl; break_if; auto.
-
find_apply_lem_hyp cronies_correct_invariant.
unfold cronies_correct in *.
intuition.
unfold votes_received_leaders in *.
match goal with | H : Leader = _ |- _ => symmetry in H end.
find_apply_hyp_hyp.
eapply wonElection_no_dup_in; eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
-
destruct (serverType_eq_dec (type (snd (nwState net x))) Leader); intuition.
find_apply_lem_hyp cronies_correct_invariant; auto.
eapply wonElection_no_dup_in; eauto using NoDup_dedup, in_dedup_was_in, dedup_In.
