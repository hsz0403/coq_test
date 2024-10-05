Require Import VerdiRaft.Raft.
Require Import VerdiRaft.CommonTheorems.
Require Import VerdiRaft.TermSanityInterface.
Section TermSanityProof.
Context {orig_base_params : BaseParams}.
Context {one_node_params : OneNodeParams orig_base_params}.
Context {raft_params : RaftParams orig_base_params}.
Instance tsi : term_sanity_interface.
Proof.
split.
auto using no_entries_past_current_term_invariant.
End TermSanityProof.

Lemma doLeader_spec : forall h st os st' ps, doLeader st h = (os, st', ps) -> log st' = log st /\ currentTerm st' = currentTerm st.
Proof using.
intros.
unfold doLeader in *.
repeat break_match; find_inversion; subst; auto.
