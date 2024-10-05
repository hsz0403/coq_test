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

Lemma processPackets_correct : forall n l n' l', processPackets n l = (n', l') -> forall p, In p l' -> n' > (tmNum (snd p)).
Proof using.
induction l; intros; simpl in *.
-
find_inversion.
simpl in *.
intuition.
-
break_match.
find_inversion.
simpl in *.
intuition.
+
subst.
simpl.
omega.
+
Admitted.

Lemma processPackets_num_monotonic : forall n l n' l', processPackets n l = (n', l') -> n' >= n.
Proof using.
induction l; intros; simpl in *.
-
intros.
find_inversion.
intuition.
-
break_match.
find_inversion.
find_insterU.
find_insterU.
conclude_using eauto.
Admitted.

Lemma processPackets_ge_start : forall n l n' l', processPackets n l = (n', l') -> forall p, In p l' -> n <= (tmNum (snd p)).
Proof using.
induction l; intros; simpl in *.
-
invcs H.
intuition.
-
break_match.
invcs H.
intuition.
+
subst.
simpl.
apply processPackets_num_monotonic in Heqp0.
intuition.
+
specialize (IHl n0 l0).
Admitted.

Lemma processPackets_nums_unique : forall n l n' l' p p', processPackets n l = (n', l') -> In p l' -> In p' l' -> p <> p' -> (tmNum (snd p)) <> (tmNum (snd p')).
Proof using.
induction l; intros; simpl in *.
-
invcs H.
intuition.
-
break_match.
invcs H.
intuition.
+
subst.
intuition.
+
subst.
simpl in *.
apply processPackets_correct with (p := p') in Heqp0; intuition.
+
subst.
simpl in *.
apply processPackets_correct with (p := p) in Heqp0; intuition.
+
Admitted.

Lemma processPackets_NoDup : forall n l n' l', processPackets n l = (n', l') -> NoDup l'.
Proof using.
induction l; intros.
-
simpl in *.
find_inversion.
constructor.
-
simpl in *.
break_match.
find_inversion.
specialize (IHl n0 l0).
concludes.
constructor; auto.
intro.
eapply processPackets_correct in H; eauto.
simpl in *.
Admitted.

Lemma processPackets_preserves_messages : forall n l, map (fun p => (fst p, tmMsg (snd p))) (snd (processPackets n l)) = l.
Proof using.
induction l.
-
auto.
-
simpl.
break_match.
simpl in *.
rewrite IHl.
destruct a.
Admitted.

Definition pkt_eq_dec (x y : seq_num_packet) : {x = y} + {x <> y}.
decide equality.
-
apply msg_eq_dec.
-
apply name_eq_dec.
-
Admitted.

Lemma network_eq (net net' : orig_network) : nwState net = nwState net' -> nwPackets net = nwPackets net' -> net = net'.
Proof using.
intros; destruct net, net'.
simpl in *.
subst.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma revertNetwork_In : forall net (p : seq_num_packet), In p (nwPackets net) -> ~ In (tmNum (pBody p)) (assoc_default name_eq_dec (tdSeen (nwState net (pDst p))) (pSrc p) []) -> In (revertPacket p) (nwPackets (revertNetwork net)).
Proof using.
intros.
unfold revertNetwork.
simpl in *.
in_crush.
apply filter_In.
intuition.
-
apply dedup_In.
auto.
-
Admitted.

Lemma revertNetwork_packets : forall xs net (p : seq_num_packet) ys, ~ In (tmNum (pBody p)) (assoc_default name_eq_dec (tdSeen (nwState net (pDst p))) (pSrc p) []) -> nwPackets net = xs ++ p :: ys -> exists xs' ys', nwPackets (revertNetwork net) = xs' ++ (revertPacket p) :: ys'.
Proof using.
intros.
apply in_split.
Admitted.

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
Admitted.

Lemma processPackets_seq_eq : forall n l n' l' x y, processPackets n l = (n', l') -> In x l' -> In y l' -> tmNum (snd x) = tmNum (snd y) -> x = y.
Proof using.
induction l; intros; simpl in *.
-
find_inversion.
simpl in *.
intuition.
-
break_match.
find_inversion.
simpl in *.
intuition; subst; simpl in *; eauto; subst; eapply processPackets_correct in Heqp; eauto; omega.
