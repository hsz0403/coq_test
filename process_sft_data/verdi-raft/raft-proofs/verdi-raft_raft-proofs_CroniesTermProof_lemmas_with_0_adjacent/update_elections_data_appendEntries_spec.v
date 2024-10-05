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

Lemma update_elections_data_appendEntries_spec : forall h st t n pli plt es ci st' e t', update_elections_data_appendEntries h st t n pli plt es ci = st' -> In e (cronies st' t') -> In e (cronies (fst st) t').
Proof using.
intros.
unfold update_elections_data_appendEntries in *.
repeat break_match; repeat find_rewrite; subst; simpl in *; auto.
