Require Import VerdiRaft.Raft.
Require Import VerdiRaft.RaftRefinementInterface.
Require Import VerdiRaft.SpecLemmas.
Require Import VerdiRaft.RefinementSpecLemmas.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import VerdiRaft.VotesLeCurrentTermInterface.
Set Bullet Behavior "Strict Subproofs".
Section VotesLeCurrentTerm.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Context {rri : raft_refinement_interface}.
Ltac start_proof := cbn [nwState]; intros; subst; repeat find_higher_order_rewrite; update_destruct; rewrite_update; cbn [fst snd] in *; eauto.
Instance vlcti : votes_le_current_term_interface.
Proof.
split.
auto using votes_le_current_term_invariant.
End VotesLeCurrentTerm.

Lemma votes_le_current_term_append_entries : refined_raft_net_invariant_append_entries votes_le_currentTerm.
Proof using.
unfold refined_raft_net_invariant_append_entries, votes_le_currentTerm.
start_proof.
rewrite @votes_same_append_entries in *.
find_apply_lem_hyp handleAppendEntries_currentTerm.
find_apply_hyp_hyp.
eauto using le_trans.
