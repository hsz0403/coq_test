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

Lemma cronies_term_request_vote : refined_raft_net_invariant_request_vote cronies_term.
Proof using.
unfold refined_raft_net_invariant_request_vote, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp handleRequestVote_spec.
find_eapply_lem_hyp update_elections_data_requestVote_spec; eauto.
eapply le_trans; [|eauto]; eauto.
