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

Lemma handleClientRequest_messages : forall h d client id c os d' ms, handleClientRequest h d client id c = (os, d', ms) -> (forall m, In m ms -> ~ is_append_entries (snd m)).
Proof using.
intros.
unfold handleClientRequest in *.
break_match; find_inversion; subst; intuition.
