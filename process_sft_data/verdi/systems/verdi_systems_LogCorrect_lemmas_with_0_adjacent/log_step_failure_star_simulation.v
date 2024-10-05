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

Lemma log_step_failure_star_simulation : forall net failed tr, step_failure_disk_ops_star step_failure_disk_ops_init (failed, net) tr -> step_failure_star step_failure_init (failed, revertLogNetwork net) tr.
Proof using.
intros net failed tr H_star.
remember step_failure_disk_ops_init as y in *.
change failed with (fst (failed, net)).
change net with (snd (failed, net)) at 2.
revert Heqy.
induction H_star using refl_trans_1n_trace_n1_ind; intro H_init.
-
find_rewrite.
simpl; unfold revertLogNetwork; simpl.
unfold step_failure_init, step_async_init.
constructor.
-
concludes.
destruct x' as (failed', net').
destruct x'' as (failed'', net'').
subst.
apply RT1n_step with (y := (failed', revertLogNetwork net')).
+
apply IHH_star1.
+
eapply log_step_failure_step; eauto.
