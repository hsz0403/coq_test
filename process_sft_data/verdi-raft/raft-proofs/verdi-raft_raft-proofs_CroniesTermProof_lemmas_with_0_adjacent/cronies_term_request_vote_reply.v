Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.CommonTheorems.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.CroniesTermInterface.
Section CroniesTermProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Instance cti : cronies_term_interface.
Proof.
split.
auto using cronies_term_invariant.
End CroniesTermProof.

Lemma cronies_term_request_vote_reply : refined_raft_net_invariant_request_vote_reply cronies_term.
Proof using.
unfold refined_raft_net_invariant_request_vote_reply, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
match goal with | H : forall _, st' _ = _ |- _ => clear H end.
unfold update_elections_data_requestVoteReply in *.
match goal with | |- context [handleRequestVoteReply ?h ?st ?h' ?t ?v] => remember (handleRequestVoteReply h st h' t v) as new_state end.
find_copy_apply_lem_hyp handleRequestVoteReply_spec.
intuition.
-
unfold update_elections_data_requestVoteReply in *.
break_match; simpl in *; repeat find_rewrite; eauto; break_match; eauto; subst; repeat find_reverse_rewrite; intuition.
-
unfold update_elections_data_requestVoteReply in *.
break_match; simpl in *; try solve [subst; unfold raft_data in *; congruence].
eapply le_trans; [|eauto]; eauto.
