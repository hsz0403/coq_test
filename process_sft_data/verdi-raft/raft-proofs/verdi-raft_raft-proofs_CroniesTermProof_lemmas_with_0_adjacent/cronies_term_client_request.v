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

Lemma cronies_term_client_request : refined_raft_net_invariant_client_request cronies_term.
Proof using.
unfold refined_raft_net_invariant_client_request, cronies_term, update_elections_data_client_request in *.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp handleClientRequest_spec.
repeat find_rewrite.
repeat break_match; simpl in *; eauto.
