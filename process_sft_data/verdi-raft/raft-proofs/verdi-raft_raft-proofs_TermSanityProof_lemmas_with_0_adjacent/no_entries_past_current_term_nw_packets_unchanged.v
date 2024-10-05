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

Theorem no_entries_past_current_term_nw_packets_unchanged : forall net ps' st', no_entries_past_current_term_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ False) -> no_entries_past_current_term_nw (mkNetwork ps' st').
Proof using.
unfold no_entries_past_current_term_nw in *.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition eauto.
