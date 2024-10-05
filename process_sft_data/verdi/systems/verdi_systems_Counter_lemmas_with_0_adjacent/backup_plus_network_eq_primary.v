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
omega.
