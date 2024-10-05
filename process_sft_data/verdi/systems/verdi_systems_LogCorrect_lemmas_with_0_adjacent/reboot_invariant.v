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

Lemma reboot_invariant : forall net failed tr, @step_failure_disk_ops_star _ _ log_failure_params step_failure_disk_ops_init (failed, net) tr -> forall h d dsk, do_reboot h (disk_to_channel (nwdoDisk net h)) = (d, dsk) -> log_data d = reboot (log_data (nwdoState net h)).
Proof using.
intros net failed tr H_st h d dsk H_reboot.
apply disk_correct_invariant with (h := h) in H_st.
unfold disk_correct in *.
break_exists.
intuition.
simpl in *.
unfold do_log_reboot, channel_to_log, disk_to_channel in *.
find_inversion.
simpl.
repeat match goal with | H : nwdoDisk net h _ = Some _ |- _ => rewrite H end.
unfold from_channel.
repeat rewrite IOStreamWriter.channel_wrap_unwrap in *.
rewrite serialize_deserialize_id_nil.
rewrite <- (app_nil_r (IOStreamWriter.unwrap _)).
match goal with | H : IOStreamWriter.unwrap _ = IOStreamWriter.unwrap _ |- _ => rewrite H end.
rewrite nat_serialize_deserialize_id.
rewrite (app_nil_end (IOStreamWriter.unwrap _)).
rewrite list_serialize_deserialize_id_rec.
find_rewrite.
reflexivity.
