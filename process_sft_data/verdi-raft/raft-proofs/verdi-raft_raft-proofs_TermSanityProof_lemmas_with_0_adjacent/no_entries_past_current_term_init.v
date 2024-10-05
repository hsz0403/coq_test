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

Theorem no_entries_past_current_term_init : raft_net_invariant_init (no_entries_past_current_term).
Proof using.
unfold raft_net_invariant_init, no_entries_past_current_term.
intuition.
-
unfold no_entries_past_current_term_host.
intros.
simpl in *.
intuition.
-
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
intuition.
