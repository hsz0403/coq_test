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
eauto using le_gt_trans, le_plus_l.
