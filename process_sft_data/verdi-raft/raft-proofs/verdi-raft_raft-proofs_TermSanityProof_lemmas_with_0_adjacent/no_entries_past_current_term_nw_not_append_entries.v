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

Theorem no_entries_past_current_term_nw_not_append_entries : forall net ps' p' st', no_entries_past_current_term_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ p = p') -> ~ is_append_entries (pBody p') -> no_entries_past_current_term_nw (mkNetwork ps' st').
Proof using.
intros.
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
-
unfold no_entries_past_current_term_nw in *.
eauto.
-
subst.
exfalso.
match goal with H : _ |- _ => apply H end.
repeat eexists; eauto.
