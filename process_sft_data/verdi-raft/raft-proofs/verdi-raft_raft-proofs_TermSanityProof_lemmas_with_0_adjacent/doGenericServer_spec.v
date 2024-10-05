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

Lemma doGenericServer_spec : forall h d os d' ms, doGenericServer h d = (os, d', ms) -> (log d' = log d /\ currentTerm d' = currentTerm d /\ (forall m, In m ms -> ~ is_append_entries (snd m))).
Proof using.
intros.
unfold doGenericServer in *.
repeat break_match; find_inversion; subst; intuition; use_applyEntries_spec; subst; simpl in *; auto.
