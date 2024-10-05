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

Theorem reachable_equality : true_in_reachable step_dup step_async_init sequence_equality.
Proof using.
apply true_in_reachable_reqs; unfold sequence_equality; simpl in *; intuition.
match goal with H : reachable _ _ _ |- _ => apply reachable_sane in H end.
unfold sequence_sane, sequence_equality in *.
intros.
match goal with H : step_dup _ _ _ |- _ => invcs H end; simpl in *; find_inversion.
-
unfold seq_num_net_handlers in *.
repeat do_in_app.
repeat find_rewrite.
repeat break_match; find_inversion; simpl in *; intuition; repeat do_in_map; subst; simpl in *.
+
repeat do_in_app.
intuition.
+
find_inversion.
match goal with | x : prod _ _, x' : prod _ _ |- _ => replace x with x' by (eapply processPackets_seq_eq; eauto) end; auto.
+
match goal with H : processPackets _ _ = _ |- _ => eapply processPackets_ge_start in H end; eauto.
match goal with _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ => specialize (H p); forward H; [in_crush|]; [concludes] end.
simpl in *.
repeat find_rewrite.
omega.
+
find_inversion.
match goal with H : processPackets _ _ = _ |- _ => eapply processPackets_ge_start in H end; eauto.
match goal with _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ => specialize (H p); forward H; [in_crush|]; [concludes] end.
simpl in *.
repeat find_rewrite.
omega.
+
match goal with H : forall _ _ : packet, In _ _ -> _ |- ?p = ?p' => specialize (H p p'); repeat (forward H; [in_crush|]; concludes) end; auto.
-
unfold seq_num_input_handlers in *.
repeat do_in_app.
repeat break_match; find_inversion; simpl in *; intuition; repeat do_in_map; subst; simpl in *.
+
find_inversion.
match goal with | x : prod _ _, x' : prod _ _ |- _ => replace x with x' by (eapply processPackets_seq_eq; eauto) end; auto.
+
match goal with H : processPackets _ _ = _ |- _ => eapply processPackets_ge_start in H end; eauto.
match goal with _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ => specialize (H p); forward H; [in_crush|]; [concludes] end.
simpl in *.
repeat find_rewrite.
omega.
+
find_inversion.
match goal with H : processPackets _ _ = _ |- _ => eapply processPackets_ge_start in H end; eauto.
match goal with _ : In ?p _, H : forall _ : packet, In _ _ -> _ |- _ => specialize (H p); forward H; [in_crush|]; [concludes] end.
simpl in *.
repeat find_rewrite.
omega.
-
repeat find_rewrite.
in_crush.
