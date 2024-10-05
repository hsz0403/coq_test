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

Lemma step_dup_star_revert_simulation : forall net tr, step_dup_star step_async_init net tr -> exists tr', step_async_star step_async_init (revertNetwork net) tr' /\ filterMap trace_non_empty_out tr = filterMap trace_non_empty_out tr'.
Proof using.
intros.
remember step_async_init as y in *.
revert Heqy.
induction H using refl_trans_1n_trace_n1_ind; simpl; intros.
-
find_rewrite.
exists []; simpl.
split; auto.
apply RT1nTBase.
-
concludes.
subst.
break_exists_name tr'.
break_and.
assert (H_r: reachable step_dup step_async_init x') by (exists tr1; auto).
eapply reachable_revert_step in H_r; eauto.
break_or_hyp.
*
exists (tr' ++ tr2); split.
+
eapply refl_trans_1n_trace_trans; eauto.
rewrite (app_nil_end tr2).
eapply RT1nTStep; eauto.
apply RT1nTBase.
+
rewrite filterMap_app.
rewrite filterMap_app.
find_reverse_rewrite.
reflexivity.
*
break_and.
find_rewrite.
exists tr'; split; simpl; auto.
match goal with | [H : filterMap _ _ = filterMap _ _ |- _ ] => rewrite <- H end.
rewrite filterMap_app.
destruct tr2; simpl in *; [ rewrite <- app_nil_end | idtac ]; auto.
match goal with | [H : _ = [] |- _ ] => rewrite H end.
rewrite <- app_nil_end; auto.
