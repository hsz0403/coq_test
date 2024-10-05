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

Lemma processPackets_dedup : forall processed (rest : list seq_num_packet) n' l h net, (forall p, In p rest -> In p (nwPackets net)) -> sequence_sane net -> processPackets (tdNum (nwState net h)) l = (n', processed) -> dedup pkt_eq_dec ((@send_packets _ multi_params h processed) ++ rest) = (send_packets h processed) ++ (dedup pkt_eq_dec rest).
Proof using.
intros.
simpl in *.
rewrite dedup_app; f_equal.
-
apply dedup_NoDup_id.
apply NoDup_map_injective; eauto using processPackets_NoDup.
intros.
find_inversion.
rewrite surjective_pairing at 1.
rewrite surjective_pairing.
unfold msg in *.
simpl in *.
repeat find_rewrite.
auto.
-
intuition.
subst.
find_apply_lem_hyp in_map_iff.
break_exists.
intuition.
find_eapply_lem_hyp processPackets_ge_start; eauto.
match goal with | _ : In ?p _, net : network |- _ => assert (In p (nwPackets net)) by eauto end.
unfold sequence_sane in *.
find_apply_hyp_hyp.
simpl in *.
subst.
simpl in *.
omega.
