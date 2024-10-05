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

Theorem no_entries_past_current_term_nw_no_append_entries : forall net ps' h l st', no_entries_past_current_term_nw net -> (forall p, In p ps' -> In p (nwPackets net) \/ In p (send_packets h l)) -> (forall m, In m l -> ~ is_append_entries (snd m)) -> no_entries_past_current_term_nw (mkNetwork ps' st').
Proof using.
intros.
eapply no_entries_past_current_term_nw_only_new_packets_matter; eauto.
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
do_in_map.
subst.
simpl in *.
find_apply_hyp_hyp.
exfalso.
match goal with H : _ |- _ => apply H end.
repeat eexists; eauto.
