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

Lemma reachable_seen : true_in_reachable step_dup step_async_init sequence_seen.
Proof using.
apply true_in_reachable_reqs; unfold sequence_seen; simpl in *; intuition.
find_apply_lem_hyp reachable_sane.
unfold sequence_sane in *.
match goal with H : step_dup _ _ _ |- _ => invcs H end.
-
unfold seq_num_net_handlers in *.
repeat (break_match; try find_inversion; simpl in *; eauto); match goal with | [ H : processPackets _ _ = _ |- _ ] => apply processPackets_num_monotonic in H end; try break_if; simpl in *; intuition; subst; eauto; repeat find_rewrite; (eapply lt_le_trans; [|eauto]; eauto).
*
case (name_eq_dec (pSrc p) (pDst p)); intro.
+
rewrite <- e in H2.
rewrite get_set_same_default in H2.
rewrite e in H2.
case H2; intro.
--
rewrite <- H.
rewrite <- e.
eapply H0.
apply in_or_app.
right; left.
auto.
--
eapply H1; eauto.
+
match goal with | [H: In _ (assoc_default _ (assoc_set _ _ _ _) _ _) |- _ ] => rewrite get_set_diff_default in H end; eauto.
*
case (name_eq_dec (pSrc p) h); intro.
+
rewrite <- e in H2.
rewrite get_set_same_default in H2.
rewrite e in H2.
case H2; intro.
--
rewrite <- H.
rewrite <- e.
eapply H0.
apply in_or_app.
right; left.
auto.
--
eapply H1; eauto.
+
match goal with | [H: In _ (assoc_default _ (assoc_set _ _ _ _) _ _) |- _ ] => rewrite get_set_diff_default in H end; eauto.
-
unfold seq_num_input_handlers in *.
repeat (break_match; try find_inversion; simpl in *; eauto); match goal with | [ H : processPackets _ _ = _ |- _ ] => apply processPackets_num_monotonic in H end; try break_if; simpl in *; intuition; subst; eauto; repeat find_rewrite; (eapply lt_le_trans; [|eauto]; eauto).
-
eauto.
