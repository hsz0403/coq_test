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

Lemma no_entries_past_current_term_reboot : raft_net_invariant_reboot no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_reboot, no_entries_past_current_term, no_entries_past_current_term_host, no_entries_past_current_term_nw, reboot.
intuition.
-
repeat find_higher_order_rewrite.
simpl in *.
subst.
break_if; simpl in *; intuition.
-
find_reverse_rewrite.
eauto.
