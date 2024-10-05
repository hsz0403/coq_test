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

Theorem revertNetwork_input : forall (st : seq_num_network) h (d : @data orig_base_params) l l' n, sequence_sane st -> sequence_seen st -> sequence_equality st -> processPackets (tdNum (nwState st h)) l = (n, l') -> revertNetwork (@mkNetwork _ multi_params (send_packets h l' ++ nwPackets st) (update name_eq_dec (nwState st) h (@mkseq_num_data _ orig_multi_params n (tdSeen (nwState st h)) d))) = {| nwPackets := (@send_packets _ orig_multi_params h l) ++ (nwPackets (revertNetwork st)); nwState := update name_eq_dec (nwState (revertNetwork st)) h d |}.
Proof using.
intros.
unfold revertNetwork.
simpl in *.
match goal with [ |- context [ dedup ?eq (map ?f ?l ++ ?l') ] ] => assert (dedup eq (map f l ++ l') = (map f l) ++ (dedup eq l')) by (find_eapply_lem_hyp processPackets_dedup; eauto; repeat find_rewrite; in_crush) end.
find_rewrite.
rewrite filter_app.
rewrite map_app.
f_equal.
f_equal.
-
rewrite filter_true_id.
+
match goal with | _ : processPackets ?n ?l = _ |- _ => rewrite <- (processPackets_preserves_messages n l) end.
find_rewrite.
simpl in *.
unfold revertPacket.
repeat rewrite map_map.
auto.
+
intros.
in_crush.
find_eapply_lem_hyp processPackets_ge_start; [|eauto].
repeat (break_if; simpl in *; repeat find_rewrite; intuition); unfold sequence_seen in *; find_apply_hyp_hyp; omega.
-
f_equal.
apply filter_fun_ext_eq.
intros.
repeat (break_if; simpl in *; repeat find_rewrite; intuition).
-
apply functional_extensionality.
intros; repeat break_if; simpl in *; intuition.
