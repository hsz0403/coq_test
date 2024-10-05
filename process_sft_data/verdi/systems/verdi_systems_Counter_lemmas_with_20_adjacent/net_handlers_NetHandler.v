Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Set Implicit Arguments.
Inductive Name := primary | backup.
Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
decide equality.
Defined.
Inductive Msg := inc | ack.
Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
Defined.
Inductive Input := request_inc.
Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
destruct x,y.
auto.
Defined.
Inductive Output := inc_executed.
Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
destruct x,y.
auto.
Defined.
Definition Data := nat.
Definition init_Data := 0.
Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.
Definition PrimaryNetHandler (m : Msg) : Handler Data := match m with | ack => write_output inc_executed | _ => nop end.
Definition PrimaryInputHandler (i : Input) : Handler Data := match i with | request_inc => modify S ;; send (backup, inc) end.
Definition BackupNetHandler (m : Msg) : Handler Data := match m with | inc => modify S ;; send (primary, ack) | _ => nop end.
Definition BackupInputHandler (i : Input) : Handler Data := nop.
Definition NetHandler (me : Name) (m : Msg) : Handler Data := match me with | primary => PrimaryNetHandler m | backup => BackupNetHandler m end.
Definition InputHandler (me : Name) (i : Input) : Handler Data := match me with | primary => PrimaryInputHandler i | backup => BackupInputHandler i end.
Instance Counter_BaseParams : BaseParams := { data := Data; input := Input; output := Output }.
Definition Nodes : list Name := [primary; backup].
Instance Counter_MultiParams : MultiParams Counter_BaseParams := { name := Name; name_eq_dec := Name_eq_dec; msg := Msg; msg_eq_dec := Msg_eq_dec; nodes := Nodes; all_names_nodes := all_Names_Nodes; no_dup_nodes := NoDup_Nodes; init_handlers := fun _ => init_Data; net_handlers := fun dst src msg s => runGenHandler_ignore s (NetHandler dst msg); input_handlers := fun nm i s => runGenHandler_ignore s (InputHandler nm i) }.
Definition inc_in_flight_to_backup (l : list packet) : nat := length (filterMap (fun p => if msg_eq_dec (pBody p) inc then if name_eq_dec (pDst p) backup then Some tt else None else None) l).
Definition trace_inputs (tr : list (name * (input + list output))) : nat := length (filterMap (fun e => match e with | (primary, inl i) => Some i | _ => None end) tr).
Definition trace_outputs (tr : list (name * (input + list output))) : nat := length (filterMap (fun e => match e with | (primary, inr [o]) => Some o | _ => None end) tr).
Definition ack_in_flight_to_primary (l : list packet) : nat := length (filterMap (fun p => if msg_eq_dec (pBody p) ack then if name_eq_dec (pDst p) primary then Some tt else None else None) l).

Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
Admitted.

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
Admitted.

Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
destruct x,y.
Admitted.

Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
destruct x,y.
Admitted.

Lemma all_Names_Nodes : forall n, In n Nodes.
Proof.
Admitted.

Lemma NoDup_Nodes : NoDup Nodes.
Proof.
Admitted.

Lemma input_handlers_InputHandlers : forall h i d os d' ms, input_handlers h i d = (os, d', ms) -> InputHandler h i d = (tt, os, d', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u.
Admitted.

Lemma PrimaryNetHandler_no_msgs : forall m d ms d' o u, PrimaryNetHandler m d = (u, o, d', ms) -> ms = [].
Proof.
unfold PrimaryNetHandler.
intros.
monad_unfold.
Admitted.

Lemma inc_in_flight_to_backup_app : forall xs ys, inc_in_flight_to_backup (xs ++ ys) = inc_in_flight_to_backup xs + inc_in_flight_to_backup ys.
Proof.
intros.
unfold inc_in_flight_to_backup.
rewrite filterMap_app.
rewrite app_length.
Admitted.

Lemma inc_in_flight_to_backup_cons_primary_dst : forall p, pDst p = primary -> inc_in_flight_to_backup [p] = 0.
Proof.
intros.
unfold inc_in_flight_to_backup.
simpl.
Admitted.

Lemma inc_in_flight_to_backup_nil : inc_in_flight_to_backup [] = 0.
Proof.
Admitted.

Lemma InputHandler_inc_in_flight_to_backup_preserved : forall h i d u o d' l, InputHandler h i d = (u, o, d', l) -> d' = d + inc_in_flight_to_backup (send_packets h l).
Proof.
unfold InputHandler, PrimaryInputHandler, BackupInputHandler.
simpl.
intros.
monad_unfold.
repeat break_match; find_inversion; compute; auto.
rewrite plus_comm.
Admitted.

Lemma NetHandler_inc_in_flight_to_backup_preserved : forall p d u o d' l, NetHandler (pDst p) (pBody p) d = (u, o, d', l) -> d' + inc_in_flight_to_backup (send_packets (pDst p) l) = d + inc_in_flight_to_backup [p].
Proof.
unfold NetHandler, PrimaryNetHandler, BackupNetHandler.
intros.
monad_unfold.
destruct p.
simpl in *.
Admitted.

Lemma InputHandler_backup_no_msgs : forall i d u o d' l, InputHandler backup i d = (u, o, d', l) -> l = [].
Proof.
simpl.
unfold BackupInputHandler.
intros.
monad_unfold.
find_inversion.
Admitted.

Lemma cons_is_app : forall A (x : A) xs, x :: xs = [x] ++ xs.
Proof.
Admitted.

Lemma backup_plus_network_eq_primary : forall net tr, step_async_star (params := Counter_MultiParams) step_async_init net tr -> nwState net backup + inc_in_flight_to_backup (nwPackets net) = nwState net primary.
Proof.
intros.
remember step_async_init as y in *.
revert Heqy.
induction H using refl_trans_1n_trace_n1_ind; intros; subst.
-
reflexivity.
-
concludes.
match goal with | [ H : step_async _ _ _ |- _ ] => invc H end; simpl.
+
find_apply_lem_hyp net_handlers_NetHandler.
find_copy_apply_lem_hyp NetHandler_inc_in_flight_to_backup_preserved.
repeat find_rewrite.
rewrite cons_is_app in IHrefl_trans_1n_trace1.
repeat rewrite inc_in_flight_to_backup_app in *.
destruct (pDst p) eqn:?; try rewrite update_same; try rewrite update_diff by congruence; unfold send_packets in *; simpl in *.
*
erewrite PrimaryNetHandler_no_msgs with (ms := l) in * by eauto.
rewrite inc_in_flight_to_backup_cons_primary_dst in * by auto.
simpl in *.
rewrite inc_in_flight_to_backup_nil in *.
auto with *.
*
omega.
+
find_apply_lem_hyp input_handlers_InputHandlers.
find_copy_apply_lem_hyp InputHandler_inc_in_flight_to_backup_preserved.
unfold send_packets in *.
simpl in *.
rewrite inc_in_flight_to_backup_app.
subst.
destruct h eqn:?; try rewrite update_same; try rewrite update_diff by congruence.
*
omega.
*
erewrite InputHandler_backup_no_msgs with (l := l) by eauto.
simpl.
rewrite inc_in_flight_to_backup_nil.
Admitted.

Theorem primary_ge_backup : forall net tr, step_async_star (params := Counter_MultiParams) step_async_init net tr -> nwState net backup <= nwState net primary.
Proof.
intros.
apply backup_plus_network_eq_primary in H.
Admitted.

Lemma trace_inputs_app : forall tr1 tr2, trace_inputs (tr1 ++ tr2) = trace_inputs tr1 + trace_inputs tr2.
Proof.
unfold trace_inputs.
intros.
rewrite filterMap_app.
rewrite app_length.
Admitted.

Lemma trace_outputs_app : forall tr1 tr2, trace_outputs (tr1 ++ tr2) = trace_outputs tr1 + trace_outputs tr2.
Proof.
unfold trace_outputs.
intros.
rewrite filterMap_app.
rewrite app_length.
Admitted.

Lemma ack_in_flight_to_primary_app : forall xs ys, ack_in_flight_to_primary (xs ++ ys) = ack_in_flight_to_primary xs + ack_in_flight_to_primary ys.
Proof.
unfold ack_in_flight_to_primary.
intros.
rewrite filterMap_app.
rewrite app_length.
Admitted.

Lemma ack_in_flight_to_primary_backup : forall p, pDst p = backup -> ack_in_flight_to_primary [p] = 0.
Proof.
intros.
unfold ack_in_flight_to_primary.
simpl.
Admitted.

Lemma InputHandler_trace_preserved : forall h i d u o d' l, InputHandler h i d = (u, o, d', l) -> trace_inputs [(h, inl i)] = trace_outputs [(h, inr o)] + inc_in_flight_to_backup (send_packets h l) + ack_in_flight_to_primary (send_packets h l).
Proof.
unfold InputHandler, PrimaryInputHandler, BackupInputHandler.
simpl.
intros.
monad_unfold.
Admitted.

Lemma NetHandler_trace_preserved : forall p d u o d' l, NetHandler (pDst p) (pBody p) d = (u, o, d', l) -> inc_in_flight_to_backup [p] + ack_in_flight_to_primary [p] = trace_outputs [((pDst p), inr o)] + inc_in_flight_to_backup (send_packets (pDst p) l) + ack_in_flight_to_primary (send_packets (pDst p) l).
Proof.
unfold NetHandler, PrimaryNetHandler, BackupNetHandler.
intros.
monad_unfold.
destruct p.
simpl in *.
Admitted.

Lemma trace_inputs_output : forall h os, trace_inputs [(h, inr os)] = 0.
Proof.
intros.
unfold trace_inputs.
simpl.
Admitted.

Lemma trace_outputs_input : forall h i, trace_outputs [(h, inl i)] = 0.
Proof.
intros.
unfold trace_outputs.
simpl.
Admitted.

Lemma trace_outputs_backup : forall e, trace_outputs [(backup, e)] = 0.
Proof.
Admitted.

Lemma net_handlers_NetHandler : forall h src m d os d' ms, net_handlers h src m d = (os, d', ms) -> NetHandler h m d = (tt, os, d', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u.
auto.
