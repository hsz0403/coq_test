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

Lemma reachable_revert_step : forall st st' tr, reachable step_dup step_async_init st -> step_dup st st' tr -> step_async (revertNetwork st) (revertNetwork st') tr \/ (revertNetwork st = revertNetwork st' /\ filterMap trace_non_empty_out tr = []).
Proof using.
intros.
find_copy_apply_lem_hyp reachable_sane.
find_copy_apply_lem_hyp reachable_seen.
find_copy_apply_lem_hyp reachable_equality.
break_exists.
match goal with H : step_dup _ _ _ |- _ => invcs H end.
-
unfold seq_num_net_handlers in *.
match goal with | [H : context [ if _ then _ else _ ] |- _] => revert H end.
break_if; intros.
+
right.
find_inversion.
simpl in *.
unfold revertNetwork.
simpl in *.
intuition.
f_equal.
*
f_equal.
find_rewrite.
symmetry.
match goal with | |- filter ?f _ = filter ?g _ => assert (f = g) by (apply functional_extensionality; intros; repeat break_if; repeat find_rewrite; intuition) end.
find_rewrite.
apply filter_dedup.
break_if; intuition.
*
apply functional_extensionality.
intros.
break_if; subst; intuition.
+
left.
repeat break_let.
find_inversion.
match goal with | [ H : processPackets _ _ = _, H' : net_handlers _ _ _ _ = (_, d0, _) |- _ ] => eapply revertNetwork_deliver_step with (d := d0) in H; eauto end.
break_exists.
break_and.
match goal with | [H : nwPackets _ = _ |- _ ] => eapply (StepAsync_deliver _ _ _ _ H); eauto end.
-
left.
unfold seq_num_input_handlers in *.
repeat break_let.
find_inversion.
find_eapply_lem_hyp revertNetwork_input; eauto.
econstructor 2; simpl; eauto.
-
right.
split; auto.
unfold revertNetwork.
f_equal.
f_equal.
f_equal.
simpl.
find_rewrite.
eauto using dedup_eliminates_duplicates.
