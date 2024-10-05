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

Lemma disk_correct_reboot : forall net h d ops, disk_correct (nwdoDisk net h) h (nwdoState net h) -> do_log_reboot snapshot_interval h (disk_to_channel (nwdoDisk net h)) = (d, ops) -> disk_correct (apply_ops (nwdoDisk net h) ops) h d.
Proof using.
intros net h d dsk H_correct H_reboot.
unfold do_log_reboot, disk_to_channel, channel_to_log, from_channel in *.
unfold disk_correct in *.
break_exists.
intuition.
repeat find_rewrite.
repeat rewrite IOStreamWriter.channel_wrap_unwrap in *.
repeat rewrite serialize_deserialize_id_nil in H_reboot.
rewrite <- (app_nil_r (IOStreamWriter.unwrap _)) in H_reboot.
repeat find_rewrite.
rewrite list_serialize_deserialize_id_rec in H_reboot.
find_inversion.
exists (IOStreamWriter.empty).
exists [].
exists (reboot (apply_log h x1 x0)).
intuition.
