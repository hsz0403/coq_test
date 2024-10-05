Require Import Verdi.Verdi.
Require Import FunctionalExtensionality.
Require Import Verdi.SeqNum.
Section SeqNumCorrect.
Context {orig_base_params : BaseParams}.
Context {orig_multi_params : MultiParams orig_base_params}.
Unset Regular Subst Tactic.
Set Regular Subst Tactic.
Definition orig_packet := @packet _ orig_multi_params.
Definition orig_network := @network _ orig_multi_params.
Definition seq_num_packet := @packet _ multi_params.
Definition seq_num_network := @network _ multi_params.
Definition revertPacket (p : seq_num_packet) : orig_packet := @mkPacket _ orig_multi_params (pSrc p) (pDst p) (tmMsg (pBody p)).
Definition pkt_eq_dec (x y : seq_num_packet) : {x = y} + {x <> y}.
decide equality.
-
apply msg_eq_dec.
-
apply name_eq_dec.
-
apply name_eq_dec.
Defined.
Definition revertNetwork (net: seq_num_network) : orig_network := mkNetwork (map revertPacket (filter (fun (p : seq_num_packet) => if member (tmNum (pBody p)) (assoc_default name_eq_dec (tdSeen (nwState net (pDst p))) (pSrc p) []) then false else true) (dedup pkt_eq_dec (nwPackets net)))) (fun h => (tdData (nwState net h))).
Definition sequence_sane (net : seq_num_network) := (forall p, In p (nwPackets net) -> tmNum (pBody p) < (tdNum ((nwState net) (pSrc p)))).
Definition sequence_seen (net : seq_num_network) := forall h h' n, In n (assoc_default name_eq_dec (tdSeen (nwState net h')) h []) -> n < (tdNum (nwState net h)).
Definition sequence_equality (net : seq_num_network) := forall p p', In p (nwPackets net) -> In p' (nwPackets net) -> (tmNum (pBody p)) = (tmNum (pBody p')) -> pSrc p = pSrc p' -> p = p'.
Arguments dedup _ _ _ : simpl nomatch.
End SeqNumCorrect.

Lemma reachable_sane : true_in_reachable step_dup step_async_init sequence_sane.
Proof using.
apply inductive_invariant_true_in_reachable.
unfold inductive_invariant, inductive.
unfold sequence_sane.
simpl in *.
intuition.
match goal with | [ H : step_dup _ _ _ |- _ ] => invcs H end; try find_inversion.
-
unfold seq_num_net_handlers in *.
simpl in *.
do_in_app.
intuition.
+
do_in_map.
subst; simpl in *.
repeat break_match; try find_inversion; simpl in *; intuition.
eapply processPackets_correct; eauto.
+
simpl in *.
repeat find_rewrite.
do_in_app.
repeat break_match; try find_inversion.
*
rewrite <- e.
intuition.
*
apply processPackets_num_monotonic in Heqp0.
apply lt_le_trans with (m := (tdNum (nwState a (pDst p0)))); auto.
rewrite <- e.
intuition.
*
intuition.
*
intuition.
-
unfold seq_num_input_handlers in *.
simpl in *.
do_in_app.
intuition.
+
do_in_map.
subst; simpl in *.
repeat break_match; try find_inversion; simpl in *; intuition.
eapply processPackets_correct; eauto.
+
simpl in *.
repeat break_match; try find_inversion; simpl in *; find_apply_lem_hyp processPackets_num_monotonic; find_apply_hyp_hyp; try omega.
-
in_crush; eauto with *.
