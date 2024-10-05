Require Import Verdi.Verdi.
Require Import Cheerios.Cheerios.
Require Import Verdi.Log.
Require Import FunctionalExtensionality.
Section LogCorrect.
Context {orig_base_params : BaseParams}.
Context {orig_multi_params : MultiParams orig_base_params}.
Context {orig_failure_params : FailureParams orig_multi_params}.
Context {data_serializer : Serializer data}.
Context {name_serializer : Serializer name}.
Context {msg_serializer : Serializer msg}.
Context {input_serializer : Serializer input}.
Variable snapshot_interval : nat.
Instance log_base_params : BaseParams := @log_base_params orig_base_params.
Instance log_multi_params : DiskOpMultiParams log_base_params := log_multi_params snapshot_interval.
Instance log_failure_params : DiskOpFailureParams log_multi_params := log_failure_params snapshot_interval.
Definition disk_correct dsk h st := exists s (entries : list entry) (snap : data), dsk Count = Some (serialize (length entries)) /\ dsk Log = Some s /\ IOStreamWriter.unwrap s = IOStreamWriter.unwrap (list_serialize_rec entry _ entries) /\ dsk Snapshot = Some (serialize snap) /\ log_num_entries st = length entries /\ (apply_log h snap entries = log_data st).
Definition orig_packet := @packet _ orig_multi_params.
Definition orig_network := @network _ orig_multi_params.
Definition log_packet := @do_packet _ log_multi_params.
Definition log_network := @do_network _ log_multi_params.
Definition revertPacket (p : log_packet) : orig_packet := @mkPacket _ orig_multi_params (do_pSrc p) (do_pDst p) (do_pBody p).
Definition revertLogNetwork (net: log_network) : orig_network := mkNetwork (map revertPacket (nwdoPackets net)) (fun h => (log_data (nwdoState net h))).
End LogCorrect.

Theorem log_step_failure_step : forall net net' failed failed' tr tr', @step_failure_disk_ops_star _ _ log_failure_params step_failure_disk_ops_init (failed, net) tr -> @step_failure_disk_ops _ _ log_failure_params (failed, net) (failed', net') tr' -> step_failure (failed, revertLogNetwork net) (failed', revertLogNetwork net') tr'.
Proof using.
intros.
assert (revert_packets : forall net, nwPackets (revertLogNetwork net) = map revertPacket (nwdoPackets net)) by reflexivity.
assert (revert_send : forall l h, map revertPacket (do_send_packets h l) = send_packets h l).
{
induction l.
*
reflexivity.
*
intros.
simpl.
now rewrite IHl.
}
assert (apply_if : forall h d, (fun h0 : name => log_data (if name_eq_dec h0 h then d else nwdoState net h0)) = (fun h0 : name => if name_eq_dec h0 h then log_data d else log_data (nwdoState net h0))).
{
intros.
extensionality h0.
break_if; reflexivity.
}
invcs H0.
-
unfold revertLogNetwork.
simpl.
find_rewrite.
repeat rewrite map_app.
simpl.
rewrite revert_send.
assert (revert_packet : do_pDst p = pDst (revertPacket p)) by reflexivity.
rewrite revert_packet in *.
apply StepFailure_deliver with (xs0 := map revertPacket xs) (ys0 := map revertPacket ys) (d0 := log_data d) (l0 := l).
+
reflexivity.
+
assumption.
+
simpl.
unfold log_net_handlers, log_handler_result in *.
break_let.
break_let.
break_if; find_inversion; rewrite revert_packet in *; assumption.
+
simpl.
rewrite apply_if.
reflexivity.
-
unfold revertLogNetwork.
simpl.
repeat rewrite map_app.
rewrite revert_send.
apply StepFailure_input with (d0 := log_data d) (l0 := l).
+
assumption.
+
unfold log_input_handlers, log_handler_result in *.
do 2 break_let.
break_if; find_inversion; assumption.
+
rewrite apply_if.
reflexivity.
-
unfold revertLogNetwork.
simpl.
find_rewrite.
rewrite map_app.
simpl.
apply StepFailure_drop with (xs0 := map revertPacket xs) (p0 := revertPacket p) (ys0 := map revertPacket ys).
+
reflexivity.
+
rewrite map_app.
reflexivity.
-
unfold revertLogNetwork.
simpl.
find_rewrite.
rewrite map_app.
simpl.
apply (@StepFailure_dup _ _ _ _ _ _ (revertPacket p) (map revertPacket xs) (map revertPacket ys)).
+
reflexivity.
+
reflexivity.
-
constructor.
-
apply StepFailure_reboot with (h0 := h).
+
assumption.
+
reflexivity.
+
unfold revertLogNetwork.
simpl.
apply reboot_invariant with (h := h) (d := d) (dsk := ops) in H.
*
rewrite <- H.
rewrite apply_if.
reflexivity.
*
assumption.
