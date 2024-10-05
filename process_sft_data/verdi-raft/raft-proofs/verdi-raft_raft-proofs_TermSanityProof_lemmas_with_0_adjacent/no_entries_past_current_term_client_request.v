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

Lemma no_entries_past_current_term_client_request : raft_net_invariant_client_request (no_entries_past_current_term).
Proof using.
unfold raft_net_invariant_client_request, no_entries_past_current_term.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite; break_if; eauto.
unfold handleClientRequest in *.
subst.
break_match; find_inversion; eauto.
simpl in *.
intuition.
subst; simpl in *; auto.
-
eauto using no_entries_past_current_term_nw_no_append_entries, handleClientRequest_messages.
