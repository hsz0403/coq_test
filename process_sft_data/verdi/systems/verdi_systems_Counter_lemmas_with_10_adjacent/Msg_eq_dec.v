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

Lemma net_handlers_NetHandler : forall h src m d os d' ms, net_handlers h src m d = (os, d', ms) -> NetHandler h m d = (tt, os, d', ms).
Proof.
intros.
simpl in *.
monad_unfold.
repeat break_let.
find_inversion.
destruct u.
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

Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
decide equality.
