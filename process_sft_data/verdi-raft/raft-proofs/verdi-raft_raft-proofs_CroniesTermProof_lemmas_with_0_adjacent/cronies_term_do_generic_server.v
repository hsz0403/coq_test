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

Lemma cronies_term_do_generic_server : refined_raft_net_invariant_do_generic_server cronies_term.
Proof using.
unfold refined_raft_net_invariant_do_generic_server, cronies_term.
intros.
subst.
simpl in *.
repeat find_higher_order_rewrite.
update_destruct; subst; rewrite_update; eauto.
simpl in *.
find_apply_lem_hyp doGenericServer_spec.
repeat find_rewrite.
match goal with | H : nwState ?net ?h = (?g, ?st) |- _ => replace g with (fst (nwState net h)) in *; [|rewrite H; auto]; replace st with (snd (nwState net h)) in *; [|rewrite H; auto] end; eauto.
