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

Lemma revertNetwork_deliver_step : forall (st : seq_num_network) p xs ys (d : @data orig_base_params) l l' n, sequence_sane st -> sequence_seen st -> sequence_equality st -> nwPackets st = xs ++ p :: ys -> ~ In (tmNum (pBody p)) (assoc_default name_eq_dec (tdSeen (nwState st (pDst p))) (pSrc p) []) -> processPackets (tdNum (nwState st (pDst p))) l = (n, l') -> exists xs' ys', nwPackets (revertNetwork st) = xs' ++ revertPacket p :: ys' /\ revertNetwork (@mkNetwork _ multi_params (map (fun m : name * seq_num_msg => {| pSrc := pDst p; pDst := fst m; pBody := snd m |}) l' ++ xs ++ ys) (update name_eq_dec (nwState st) (pDst p) (@mkseq_num_data _ orig_multi_params n (assoc_set name_eq_dec (tdSeen (nwState st (pDst p))) (pSrc p) (tmNum (pBody p) :: assoc_default name_eq_dec (tdSeen (nwState st (pDst p))) (pSrc p) [])) d))) = {| nwPackets := (@send_packets _ orig_multi_params (pDst p) l) ++ xs' ++ ys'; nwState := update name_eq_dec (nwState (revertNetwork st)) (pDst p) d |}.
Proof using.
intros.
simpl in *.
unfold revertNetwork.
simpl in *.
repeat find_rewrite.
match goal with [ |- context [ dedup ?eq (map ?f ?l ++ ?xs ++ ?ys) ] ] => assert (dedup eq (map f l ++ xs ++ ys) = (map f l) ++ (dedup eq (xs ++ ys))) by (find_eapply_lem_hyp processPackets_dedup; eauto; repeat find_rewrite; in_crush) end.
find_rewrite.
rewrite filter_app.
rewrite map_app.
assert (In p (nwPackets st)) by (find_rewrite; in_crush).
match goal with | H : In _ _ |- _ => apply dedup_In with (A_eq_dec := pkt_eq_dec) in H end.
find_apply_lem_hyp in_split.
break_exists.
repeat find_rewrite.
find_copy_apply_lem_hyp dedup_partition.
unfold seq_num_packet in *.
repeat find_rewrite.
assert (NoDup (x ++ p :: x0)) by (repeat find_reverse_rewrite; apply NoDup_dedup).
match goal with | [ |- context [ filter ?f (?xs ++ ?p :: ?ys) ] ] => assert (In p (filter f (xs ++ p :: ys))) by (apply filter_In; repeat break_if; intuition) end.
find_apply_lem_hyp in_split.
break_exists.
repeat find_rewrite.
exists (map revertPacket x1), (map revertPacket x2).
intuition; map_crush; auto.
simpl in *.
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
match goal with p : packet |- _ => assert (tmNum (pBody p) < tdNum (nwState st (pSrc p))) by (eapply_prop sequence_sane; find_rewrite; in_crush) end.
repeat (break_if; simpl in *; repeat find_rewrite; intuition); unfold sequence_seen in *.
--
case (name_eq_dec (pSrc p) (pDst p)); intro.
++
rewrite <- e0 in i.
rewrite get_set_same_default in i.
rewrite e0 in i.
case i; intro.
**
rewrite <- H12 in H11.
rewrite <- e0 in H11.
omega.
**
pose proof (H0 _ _ _ H12).
omega.
++
match goal with | [H: In _ (assoc_default _ (assoc_set _ _ _ _) _ _) |- _ ] => rewrite get_set_diff_default in H end; auto.
pose proof (H0 _ _ _ i).
omega.
--
pose proof (H0 _ _ _ i).
omega.
-
rewrite <- filter_except_one with (f := (fun p0 : seq_num_packet => if member (tmNum (pBody p0)) (assoc_default name_eq_dec (tdSeen (nwState st (pDst p0))) (pSrc p0) []) then false else true)) (x := p) (A_eq_dec := pkt_eq_dec).
+
unfold seq_num_packet in *.
repeat find_rewrite.
rewrite filter_app.
find_apply_lem_hyp filter_partition; intuition.
repeat find_rewrite.
eauto using map_app.
+
intros.
repeat (break_if; simpl in *; repeat find_rewrite; intuition).
--
contradict n0.
case (name_eq_dec (pSrc p) (pSrc y)); intro.
**
rewrite <- e0.
rewrite get_set_same_default.
right.
rewrite e0.
auto.
**
rewrite get_set_diff_default; auto.
--
exfalso.
match goal with H : _ = _ -> False |- _ => apply H end.
eapply_prop sequence_equality; repeat find_rewrite; in_crush.
**
find_apply_lem_hyp in_dedup_was_in.
in_crush.
**
case (name_eq_dec (pSrc p) (pSrc y)); intro.
++
rewrite e0 in i.
rewrite get_set_same_default in i.
case i; intro; intuition.
++
rewrite get_set_diff_default in i; intuition.
**
case (name_eq_dec (pSrc p) (pSrc y)); intro; auto.
rewrite get_set_diff_default in i; intuition.
+
repeat (break_if; simpl in *; intuition).
contradict n0.
rewrite get_set_same_default.
left; auto.
-
apply functional_extensionality.
intros; repeat break_if; simpl in *; intuition.
