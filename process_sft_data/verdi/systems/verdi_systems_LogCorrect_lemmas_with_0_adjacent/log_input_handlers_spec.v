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

Lemma log_input_handlers_spec : forall h m st ops out st' l dsk dsk', disk_correct dsk h st -> log_input_handlers snapshot_interval h m st = (ops, out, st', l) -> apply_ops dsk ops = dsk' -> disk_correct dsk' h st'.
Proof using.
intros.
unfold disk_correct in *.
unfold log_input_handlers, log_handler_result in *; break_if; do 2 break_let.
-
find_inversion.
simpl.
exists IOStreamWriter.empty, [], d.
intuition.
-
find_inversion.
simpl.
break_exists.
intuition.
match goal with | _ : dsk Log = Some ?s, _ : apply_log _ ?d ?entries = _ |- _ => exists (s +$+ (serialize (inl m : entry))), (entries ++ [inl m]), d end.
intuition.
+
match goal with | H : context [log_num_entries] |- _ => rewrite H end.
rewrite app_length.
simpl.
rewrite NPeano.Nat.add_1_r.
reflexivity.
+
break_match.
*
find_inversion.
reflexivity.
*
congruence.
+
cheerios_crush.
rewrite serialize_snoc.
match goal with | H : IOStreamWriter.unwrap _ = IOStreamWriter.unwrap _ |- _ => rewrite H end.
reflexivity.
+
match goal with | H : context [log_num_entries] |- _ => rewrite H end.
rewrite app_length.
simpl.
rewrite NPeano.Nat.add_1_r.
reflexivity.
+
rewrite apply_log_app.
match goal with | H : context [apply_log] |- _ => rewrite H end.
simpl.
match goal with | H : context [input_handlers] |- _ => rewrite H end.
reflexivity.
