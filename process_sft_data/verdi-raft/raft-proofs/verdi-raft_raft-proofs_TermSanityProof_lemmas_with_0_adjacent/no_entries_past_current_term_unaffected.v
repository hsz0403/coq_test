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

Lemma no_entries_past_current_term_unaffected : forall net st' ps' xs p ys d ms, nwPackets net = xs ++ p :: ys -> no_entries_past_current_term net -> (forall h : Net.name, st' h = update name_eq_dec (nwState net) (pDst p) d h) -> (forall p' : packet, In p' ps' -> In p' (xs ++ ys) \/ In p' (send_packets (pDst p) ms)) -> currentTerm (nwState net (pDst p)) <= currentTerm d -> log d = log (nwState net (pDst p)) -> (forall m, In m ms -> ~ is_append_entries (snd m)) -> no_entries_past_current_term {| nwPackets := ps'; nwState := st' |}.
Proof using.
intros.
unfold no_entries_past_current_term in *.
intuition.
-
unfold no_entries_past_current_term_host in *.
intros.
simpl in *.
find_higher_order_rewrite.
break_if; eauto.
subst.
repeat find_rewrite.
eapply le_trans; [|eauto].
eauto.
-
unfold no_entries_past_current_term_nw.
intros.
simpl in *.
find_apply_hyp_hyp.
intuition.
+
intros.
match goal with | _ : In ?p _ |- _ => assert (In p (nwPackets net)) by (find_rewrite; in_crush) end.
eapply_prop no_entries_past_current_term_nw; eauto.
+
exfalso.
do_in_map.
subst.
simpl in *.
find_apply_hyp_hyp.
find_rewrite.
repeat eexists; eauto.
