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

Lemma no_entries_past_current_term_state_same_packet_subset : raft_net_invariant_state_same_packet_subset no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_state_same_packet_subset, no_entries_past_current_term, no_entries_past_current_term_host, no_entries_past_current_term_nw.
intros.
intuition.
-
repeat find_reverse_higher_order_rewrite.
eauto.
-
find_apply_hyp_hyp.
eauto.
