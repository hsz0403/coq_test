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

Lemma no_entries_past_current_term_append_entries : raft_net_invariant_append_entries no_entries_past_current_term.
Proof using.
unfold raft_net_invariant_append_entries, no_entries_past_current_term.
intros.
find_apply_lem_hyp handleAppendEntries_spec.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite.
break_if; eauto.
subst.
find_apply_hyp_hyp.
intuition.
+
eapply le_trans; [|eauto]; eauto.
+
subst.
eapply_prop no_entries_past_current_term_nw; eauto.
-
match goal with | _ : context [{| pSrc := ?ps; pDst := ?pd; pBody := ?pb |}] |- _ => eapply no_entries_past_current_term_nw_not_append_entries with (p' := {| pSrc := ps; pDst := pd; pBody := pb |}) end; eauto.
intros.
find_apply_hyp_hyp.
find_rewrite.
in_crush.
