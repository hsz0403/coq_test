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

Lemma handleRequestVoteReply_preserves_candidate_entries : forall net h h' t r st' e, st' = handleRequestVoteReply h (snd (nwState net h)) h' t r -> refined_raft_intermediate_reachable net -> candidateEntries e (nwState net) -> candidateEntries e (update name_eq_dec (nwState net) h (update_elections_data_requestVoteReply h h' t r (nwState net h), st')).
Proof using cci.
unfold candidateEntries.
intros.
break_exists.
break_and.
exists x.
split; rewrite update_fun_comm; simpl; rewrite update_fun_comm; simpl; update_destruct; subst; rewrite_update; auto; try (unfold update_elections_data_requestVoteReply in *; repeat break_match; simpl in *; auto; break_if; simpl in *; repeat find_rewrite; auto); match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?r] => remember (handleRequestVoteReply h st h' t r) as new_state end; find_apply_lem_hyp handleRequestVoteReply_spec; intuition; repeat find_rewrite; intuition.
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
