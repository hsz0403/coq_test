Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import StructTact.Fin.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import Verdi.StatePacketPacketDecomposition.
Require Import Verdi.LabeledNet.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Set Implicit Arguments.
Section LockServ.
Variable num_Clients : nat.
Definition Client_index := (fin num_Clients).
Inductive Name := | Client : Client_index -> Name | Server : Name.
Definition list_Clients := map Client (all_fin num_Clients).
Definition Name_eq_dec : forall a b : Name, {a = b} + {a <> b}.
decide equality.
apply fin_eq_dec.
Inductive Msg := | Lock : Msg | Unlock : Msg | Locked : Msg.
Definition Msg_eq_dec : forall a b : Msg, {a = b} + {a <> b}.
decide equality.
Definition Input := Msg.
Definition Output := Msg.
Record Data := mkData { queue : list Client_index ; held : bool }.
Definition init_data (n : Name) : Data := mkData [] false.
Inductive Label := | InputLock : Client_index -> Label | InputUnlock : Client_index -> Label | MsgUnlock : Label | MsgLock : Client_index -> Label | MsgLocked : Client_index -> Label | Nop | Silent.
Definition Handler (S : Type) := GenHandler (Name * Msg) S Output Label.
Definition ClientNetHandler (i : Client_index) (m : Msg) : Handler Data := match m with | Locked => (put (mkData [] true)) ;; write_output Locked ;; ret (MsgLocked i) | _ => ret Nop end.
Definition ClientIOHandler (i : Client_index) (m : Msg) : Handler Data := match m with | Lock => send (Server, Lock) ;; ret (InputLock i) | Unlock => data <- get ;; when (held data) (put (mkData [] false) >> send (Server, Unlock));; ret (InputUnlock i) | _ => ret Nop end.
Definition ServerNetHandler (src : Name) (m : Msg) : Handler Data := st <- get ;; let q := queue st in match m with | Lock => match src with | Server => ret Nop | Client c => when (null q) (send (src, Locked)) >> put (mkData (q++[c]) (held st)) >> ret (MsgLock c) end | Unlock => match q with | _ :: x :: xs => put (mkData (x :: xs) (held st)) >> send (Client x, Locked) | _ => put (mkData [] (held st)) end ;; ret MsgUnlock | _ => ret Nop end.
Definition ServerIOHandler (m : Msg) : Handler Data := ret Nop.
Definition NetHandler (nm src : Name) (m : Msg) : Handler Data := match nm with | Client c => ClientNetHandler c m | Server => ServerNetHandler src m end.
Definition InputHandler (nm : Name) (m : Msg) : Handler Data := match nm with | Client c => ClientIOHandler c m | Server => ServerIOHandler m end.
Ltac handler_unfold := repeat (monad_unfold; unfold NetHandler, InputHandler, ServerNetHandler, ClientNetHandler, ClientIOHandler, ServerIOHandler in *).
Definition Nodes := Server :: list_Clients.
Global Instance LockServ_BaseParams : BaseParams := { data := Data ; input := Input ; output := Output }.
Global Instance LockServ_LabeledParams : LabeledMultiParams LockServ_BaseParams := { lb_name := Name ; lb_msg := Msg ; lb_msg_eq_dec := Msg_eq_dec ; lb_name_eq_dec := Name_eq_dec ; lb_nodes := Nodes ; lb_all_names_nodes := In_n_Nodes ; lb_no_dup_nodes := nodup ; label := Label ; label_silent := Silent; lb_init_handlers := init_data ; lb_net_handlers := fun dst src msg s => runGenHandler s (NetHandler dst src msg) ; lb_input_handlers := fun nm msg s => runGenHandler s (InputHandler nm msg) }.
Global Instance LockServ_MultiParams : MultiParams LockServ_BaseParams := unlabeled_multi_params.
Definition mutual_exclusion (sigma : name -> data) : Prop := forall m n, held (sigma (Client m)) = true -> held (sigma (Client n)) = true -> m = n.
Definition locks_correct (sigma : name -> data) : Prop := forall n, held (sigma (Client n)) = true -> exists t, queue (sigma Server) = n :: t.
Definition valid_unlock q h c p := pSrc p = Client c /\ (exists t, q = c :: t) /\ h = false.
Definition locks_correct_unlock (sigma : name -> data) (p : packet) : Prop := pBody p = Unlock -> exists c, valid_unlock (queue (sigma Server)) (held (sigma (Client c))) c p.
Definition valid_locked q h c p := pDst p = Client c /\ (exists t, q = c :: t) /\ h = false.
Definition locks_correct_locked (sigma : name -> data) (p : packet) : Prop := pBody p = Locked -> exists c, valid_locked (queue (sigma Server)) (held (sigma (Client c))) c p.
Definition LockServ_network_invariant (sigma : name -> data) (p : packet) : Prop := locks_correct_unlock sigma p /\ locks_correct_locked sigma p.
Definition LockServ_network_network_invariant (p q : packet) : Prop := (pBody p = Unlock -> pBody q = Unlock -> False) /\ (pBody p = Locked -> pBody q = Unlock -> False) /\ (pBody p = Unlock -> pBody q = Locked -> False) /\ (pBody p = Locked -> pBody q = Locked -> False).
Ltac set_up_input_handlers := intros; find_apply_lem_hyp InputHandler_cases; intuition idtac; try break_exists; intuition idtac; subst; repeat find_rewrite; simpl in *; intuition idtac; repeat find_inversion; try now rewrite update_nop_ext.
Definition at_head_of_queue sigma c := (exists t, queue (sigma Server) = c :: t).
Ltac set_up_net_handlers := intros; match goal with | [ H : context [ NetHandler (pDst ?p) _ _ _ ] |- _ ] => destruct (pDst p) eqn:? end; simpl in *; [find_apply_lem_hyp ClientNetHandler_cases | find_apply_lem_hyp ServerNetHandler_cases; intuition; try break_exists ]; intuition; subst; simpl in *; intuition; repeat find_rewrite; repeat find_inversion; simpl in *; try now rewrite update_nop_ext.
Ltac unlabeled_unfold := unfold unlabeled_net_handlers, unlabeled_input_handlers in *.
Instance LockServ_Decompositition : Decomposition _ LockServ_MultiParams.
apply Build_Decomposition with (state_invariant := locks_correct) (network_invariant := LockServ_network_invariant) (network_network_invariant := LockServ_network_network_invariant); simpl; intros; monad_unfold; unlabeled_unfold; repeat break_let; repeat find_inversion.
-
auto using nwnw_sym.
-
auto using locks_correct_init.
-
eauto using locks_correct_input_handlers.
-
unfold LockServ_network_invariant in *.
intuition.
eauto using locks_correct_net_handlers.
-
unfold LockServ_network_invariant in *.
intuition eauto using locks_correct_unlock_input_handlers_old, locks_correct_locked_input_handlers_old.
-
unfold LockServ_network_invariant in *.
intuition eauto using locks_correct_unlock_input_handlers_new, locks_correct_locked_input_handlers_new.
-
unfold LockServ_network_invariant in *.
intuition eauto using locks_correct_unlock_net_handlers_old, locks_correct_locked_net_handlers_old.
-
unfold LockServ_network_invariant in *.
intuition eauto using locks_correct_unlock_net_handlers_new, locks_correct_locked_net_handlers_new.
-
eauto using LockServ_nwnw_input_handlers_old_new.
-
eauto using LockServ_nwnw_input_handlers_new_new.
-
eauto using LockServ_nwnw_net_handlers_old_new.
-
eauto using LockServ_nwnw_net_handlers_new_new.
Defined.
Fixpoint last_holder' (holder : option Client_index) (trace : list (name * (input + list output))) : option Client_index := match trace with | [] => holder | (Client n, inl Unlock) :: tr => match holder with | None => last_holder' holder tr | Some m => if fin_eq_dec _ n m then last_holder' None tr else last_holder' holder tr end | (Client n, inr [Locked]) :: tr => last_holder' (Some n) tr | (n, _) :: tr => last_holder' holder tr end.
Fixpoint trace_mutual_exclusion' (holder : option Client_index) (trace : list (name * (input + list output))) : Prop := match trace with | [] => True | (Client n, (inl Unlock)) :: tr' => match holder with | Some m => if fin_eq_dec _ n m then trace_mutual_exclusion' None tr' else trace_mutual_exclusion' holder tr' | _ => trace_mutual_exclusion' holder tr' end | (n, (inl _)) :: tr' => trace_mutual_exclusion' holder tr' | (Client n, (inr [Locked])) :: tr' => match holder with | None => trace_mutual_exclusion' (Some n) tr' | Some _ => False end | (_, (inr [])) :: tr' => trace_mutual_exclusion' holder tr' | (_, (inr _)) :: tr' => False end.
Definition trace_mutual_exclusion (trace : list (name * (input + list output))) : Prop := trace_mutual_exclusion' None trace.
Definition last_holder (trace : list (name * (input + list output))) : option Client_index := last_holder' None trace.
Ltac my_update_destruct := match goal with | [H : context [ update _ _ ?x _ ?y ] |- _ ] => destruct (Name_eq_dec x y) | [ |- context [ update _ _ ?x _ ?y ] ] => destruct (Name_eq_dec x y) end.
Definition message_enables_label p l := forall net, In p (nwPackets net) -> lb_step_ex lb_step_async l net.
Definition message_delivered_label p l := forall l' net net' tr, lb_step_async net l' net' tr -> In p (nwPackets net) -> ~ In p (nwPackets net') -> l = l'.
Definition label_eq_dec : forall x y : label, {x = y} + {x <> y}.
Proof using.
decide equality; apply fin_eq_dec.
Ltac coinductive_case CIH := apply W_tl; simpl in *; auto; apply CIH; simpl in *; auto.
End LockServ.

Lemma last_holder'_unlock_none : forall tr h c, last_holder' h tr = Some c -> last_holder' h (tr ++ [(Client c, inl Unlock)]) = None.
Proof using.
induction tr; intros; simpl in *; repeat break_match; intuition.
Admitted.

Lemma last_holder_unlock_none : forall tr c, last_holder tr = Some c -> last_holder (tr ++ [(Client c, inl Unlock)]) = None.
Proof using.
intros.
apply last_holder'_unlock_none.
Admitted.

Lemma last_holder_some_unlock_inv : forall tr h c n, last_holder' h (tr ++ [(Client c, inl Unlock)]) = Some n -> last_holder' h tr = Some n.
Proof using.
Admitted.

Lemma last_holder'_neq_unlock_extend : forall tr h n c, last_holder' h tr = Some n -> n <> c -> last_holder' h (tr ++ [(Client c, inl Unlock)]) = Some n.
Proof using.
Admitted.

Lemma LockServ_mutual_exclusion_trace : forall st tr, step_async_star step_async_init st tr -> trace_mutual_exclusion tr /\ (forall n, last_holder tr = Some n -> held (nwState st (Client n)) = true) /\ (forall n, held (nwState st (Client n)) = true -> last_holder tr = Some n).
Proof using.
apply cross_relation; intros.
-
intuition.
+
red.
red.
auto.
+
unfold last_holder in *.
simpl in *.
discriminate.
+
unfold last_holder in *.
simpl in *.
discriminate.
-
match goal with | [ H : step_async _ _ _ |- _ ] => invcs H end; monad_unfold; unlabeled_unfold; unfold lb_net_handlers, lb_input_handlers in *; simpl in *; repeat break_let; repeat find_inversion.
+
unfold NetHandler in *.
break_match.
*
find_apply_lem_hyp ClientNetHandler_cases; eauto.
break_and.
{
break_or_hyp.
-
intuition; subst.
+
apply trace_mutex'_no_out_extend; auto.
+
rewrite update_nop_ext.
find_apply_lem_hyp last_holder'_no_out_inv.
auto.
+
match goal with | [ H : _ |- _ ] => rewrite update_nop in H end.
find_apply_hyp_hyp.
apply last_holder'_no_out_extend.
auto.
-
intuition; subst.
+
apply trace_mutex'_locked_extend.
auto.
destruct (last_holder' None tr) eqn:?; auto.
find_apply_hyp_hyp.
erewrite locked_in_flight_all_clients_false in * by eauto using locks_correct_locked_invariant, reachable_intro, locks_correct_invariant.
discriminate.
+
my_update_destruct; try find_inversion; rewrite_update; auto.
find_apply_lem_hyp last_holder'_locked_some_eq.
congruence.
+
my_update_destruct; try find_inversion; rewrite_update.
*
apply last_holder'_locked_extend.
*
erewrite locked_in_flight_all_clients_false in * by eauto using locks_correct_locked_invariant, reachable_intro, locks_correct_invariant.
discriminate.
}
*
{
find_apply_lem_hyp ServerNetHandler_cases.
break_and.
subst.
repeat split.
-
apply trace_mutex'_no_out_extend.
auto.
-
intros.
my_update_destruct; try discriminate.
rewrite_update.
find_apply_lem_hyp last_holder'_no_out_inv.
auto.
-
intros.
my_update_destruct; try discriminate; rewrite_update.
apply last_holder'_no_out_extend.
auto.
}
+
unfold InputHandler in *.
break_match.
*
unfold ClientIOHandler in *.
{
monad_unfold.
repeat break_match; repeat find_inversion; intuition; repeat rewrite snoc_assoc in *; try apply trace_mutex'_no_out_extend; try find_apply_lem_hyp last_holder'_no_out_inv; try (apply last_holder'_no_out_extend; auto).
-
apply trace_mutual_exclusion'_extend_input; auto.
congruence.
-
rewrite update_nop_ext.
find_apply_lem_hyp last_holder'_input_inv; try congruence.
auto.
-
match goal with | [ H : _ |- _ ] => rewrite update_nop in H end.
apply last_holder'_input_extend; auto.
congruence.
-
apply trace_mutex'_unlock_extend; auto.
-
rewrite last_holder_unlock_none in *; auto.
discriminate.
-
my_update_destruct; try find_inversion; rewrite_update.
+
discriminate.
+
assert (mutual_exclusion (nwState st)) by eauto using mutual_exclusion_invariant, reachable_intro.
unfold mutual_exclusion in *.
assert (c = n) by eauto.
congruence.
-
apply trace_mutex'_unlock_extend.
auto.
-
rewrite update_nop.
find_apply_lem_hyp last_holder_some_unlock_inv.
auto.
-
match goal with | [ H : _ |- _ ] => rewrite update_nop in H end.
assert (n <> c) by congruence.
find_apply_hyp_hyp.
apply last_holder'_neq_unlock_extend; auto.
-
apply trace_mutual_exclusion'_extend_input; auto.
congruence.
-
rewrite update_nop_ext.
find_apply_lem_hyp last_holder'_input_inv; try congruence.
auto.
-
match goal with | [ H : _ |- _ ] => rewrite update_nop in H end.
apply last_holder'_input_extend; auto.
congruence.
}
*
unfold ServerIOHandler in *.
monad_unfold.
find_inversion.
{
intuition; repeat rewrite snoc_assoc in *.
-
apply trace_mutex'_no_out_extend.
apply trace_mutual_exclusion'_extend_input_server.
auto.
-
find_apply_lem_hyp last_holder'_no_out_inv.
rewrite update_nop.
find_apply_lem_hyp last_holder'_input_inv_server.
auto.
-
apply last_holder'_no_out_extend; auto.
rewrite_update.
unfold last_holder.
rewrite last_holder'_server_extend.
auto.
Admitted.

Lemma head_grant_state_unlock : forall st tr c t, step_async_star step_async_init st tr -> queue (nwState st Server) = c :: t -> (In (mkPacket Server (Client c) Locked) (nwPackets st)) \/ (held (nwState st (Client c)) = true) \/ (In (mkPacket (Client c) Server Unlock) (nwPackets st)).
Proof using.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
prep_induction H.
induction H; intros; subst.
-
discriminate.
-
match goal with | [ H : step_async _ _ _ |- _ ] => invcs H end; unlabeled_unfold; unfold lb_net_handlers, lb_input_handlers in *; simpl in *; monad_unfold; repeat break_let; repeat find_inversion.
+
unfold NetHandler in *.
break_match; rewrite_update.
*
find_apply_lem_hyp ClientNetHandler_cases.
intuition.
--
subst.
rewrite update_nop_ext.
find_apply_lem_hyp IHrefl_trans_n1_trace; auto; [idtac].
repeat find_rewrite.
simpl.
in_crush.
discriminate.
--
subst.
find_apply_lem_hyp refl_trans_n1_1n_trace.
find_apply_lem_hyp reachable_intro.
match goal with | [ H : reachable _ _ _ |- _ ] => let H' := fresh H in pose H as H'; eapply locks_correct_locked_invariant with (p := p) in H'; [| now repeat find_rewrite; in_crush]; eapply locks_correct_locked_at_head in H'; eauto end.
unfold at_head_of_queue in *.
break_exists.
find_rewrite.
find_inversion.
rewrite_update.
auto.
*
find_apply_lem_hyp ServerNetHandler_cases.
intuition.
--
break_exists.
intuition.
++
subst.
repeat find_rewrite.
simpl in *.
find_inversion.
auto.
++
subst.
repeat find_rewrite.
destruct (queue (nwState x' Server)); try congruence.
simpl in *.
find_inversion.
do 2 insterU IHrefl_trans_n1_trace.
repeat conclude_using eauto.
intuition.
**
in_crush.
discriminate.
**
in_crush.
discriminate.
--
congruence.
--
break_exists.
intuition.
subst.
simpl.
repeat find_rewrite.
find_inversion.
auto.
--
subst.
simpl.
find_apply_hyp_hyp.
intuition.
++
repeat find_rewrite.
in_crush.
discriminate.
++
repeat find_rewrite.
in_crush.
+
find_apply_lem_hyp InputHandler_cases.
intuition.
*
break_exists.
break_and.
subst.
rewrite_update.
find_apply_hyp_hyp.
intuition.
--
subst.
rewrite update_nop_ext.
auto.
--
find_apply_lem_hyp refl_trans_n1_1n_trace.
find_apply_lem_hyp reachable_intro.
match goal with | [ H : reachable _ _ _ |- _ ] => pose H as Hmutex; eapply mutual_exclusion_invariant in Hmutex end.
unfold mutual_exclusion in *.
assert (c = x) by auto.
clear Hmutex.
subst.
simpl.
auto.
--
subst.
rewrite_update.
auto.
*
subst.
simpl.
rewrite update_nop_ext in *.
Admitted.

Lemma InputHandler_lbcases : forall h i st l out st' ms, InputHandler h i st = (l, out, st', ms) -> (exists c, h = Client c /\ ((i = Lock /\ out = [] /\ st' = st /\ ms = [(Server, Lock)] /\ l = InputLock c) \/ (l = InputUnlock c /\ i = Unlock /\ out = [] /\ held st' = false /\ ((held st = true /\ ms = [(Server, Unlock)]) \/ (st' = st /\ ms = []))))) \/ (out = [] /\ st' = st /\ ms = [] /\ l = Nop).
Proof using.
handler_unfold.
intros.
repeat break_match; repeat tuple_inversion; subst; simpl in *; subst; simpl in *.
-
left.
eexists.
intuition.
-
left.
eexists.
intuition.
-
left.
eexists.
intuition.
-
auto.
-
Admitted.

Lemma ClientNetHandler_lbcases : forall c m st l out st' ms, ClientNetHandler c m st = (l, out, st', ms) -> ms = [] /\ ((st' = st /\ out = [] /\ l = Nop) \/ (m = Locked /\ out = [Locked] /\ held st' = true /\ l = MsgLocked c)).
Proof using.
handler_unfold.
intros.
Admitted.

Lemma ServerNetHandler_lbcases : forall src m st l out st' ms, ServerNetHandler src m st = (l, out, st', ms) -> out = [] /\ ((exists c, src = Client c /\ (m = Lock /\ l = MsgLock c /\ queue st' = queue st ++ [c] /\ ((queue st = [] /\ ms = [(Client c, Locked)]) \/ (queue st <> [] /\ ms = [])))) \/ ((m = Unlock /\ l = MsgUnlock /\ queue st' = tail (queue st) /\ ((queue st' = [] /\ ms = []) \/ (exists next t, queue st' = next :: t /\ ms = [(Client next, Locked)])))) \/ ms = [] /\ st' = st /\ l = Nop).
Proof using.
handler_unfold.
intros.
repeat break_match; repeat tuple_inversion; subst.
-
find_apply_lem_hyp null_sound.
find_rewrite.
simpl.
intuition.
left.
eexists.
intuition.
-
simpl.
find_apply_lem_hyp null_false_neq_nil.
intuition.
left.
eexists.
intuition.
-
simpl.
intuition.
-
simpl.
destruct st; simpl in *; subst; intuition.
-
simpl in *.
intuition.
-
simpl in *.
intuition eauto.
-
simpl.
Admitted.

Lemma Lock_enables_MsgLock : forall i, message_enables_label (mkPacket (Client i) Server Lock) (MsgLock i).
Proof using.
unfold message_enables_label.
intros.
find_apply_lem_hyp in_split.
break_exists_name xs.
break_exists_name ys.
unfold enabled.
destruct (ServerNetHandler (Client i) Lock (nwState net Server)) eqn:?.
destruct p.
destruct p.
cut (l0 = MsgLock i); intros.
subst.
-
repeat eexists.
econstructor; eauto.
-
handler_unfold.
Admitted.

Lemma In_split_not_In : forall A (p : A) p' xs ys zs, In p (xs ++ p' :: ys) -> ~ In p (zs ++ xs ++ ys) -> p = p'.
Proof using.
intros.
find_apply_lem_hyp in_app_iff.
Admitted.

Lemma Lock_delivered_MsgLock : forall i, message_delivered_label (mkPacket (Client i) Server Lock) (MsgLock i).
Proof using.
unfold message_delivered_label.
intros.
invcs H.
-
repeat find_rewrite.
find_eapply_lem_hyp In_split_not_In; eauto.
subst.
monad_unfold.
simpl in *.
handler_unfold.
repeat break_match; repeat find_inversion; auto.
-
unfold not in *.
find_false.
apply in_app_iff; auto.
-
Admitted.

Definition label_eq_dec : forall x y : label, {x = y} + {x <> y}.
Proof using.
Admitted.

Lemma messages_trigger_labels : forall l p, message_enables_label p l -> message_delivered_label p l -> forall s, lb_step_execution lb_step_async s -> In p (nwPackets (evt_a (hd s))) -> weak_until (now (enabled lb_step_async l)) (now (occurred l)) s.
Proof using.
intros l p Henabled Hdelivered.
cofix c.
destruct s.
destruct e.
simpl.
intros Hexec Hin.
invcs Hexec.
destruct (label_eq_dec l evt_l).
-
subst evt_l.
apply W0.
simpl.
reflexivity.
-
apply W_tl.
+
simpl.
unfold message_enables_label in *.
unfold enabled.
simpl.
now auto.
+
simpl.
apply c; auto.
simpl.
match goal with | |- In ?p ?ps => destruct (In_dec packet_eq_dec p ps) end; auto.
unfold message_delivered_label in *.
Admitted.

Lemma message_labels_eventually_occur : forall l p, l <> label_silent -> message_enables_label p l -> message_delivered_label p l -> forall s, weak_fairness lb_step_async label_silent s -> lb_step_execution lb_step_async s -> In p (nwPackets (evt_a (hd s))) -> eventually (now (occurred l)) s.
Proof using.
intros.
find_eapply_lem_hyp messages_trigger_labels; eauto.
find_apply_lem_hyp weak_until_until_or_always.
intuition.
-
now eauto using until_eventually.
-
find_apply_lem_hyp always_continuously.
eapply_prop_hyp weak_fairness continuously; auto.
destruct s.
Admitted.

Lemma Nth_app : forall A (l : list A) l' a n, Nth l n a -> Nth (l ++ l') n a.
Proof using.
induction l; intros; simpl in *; try solve_by_inversion.
invcs H.
-
constructor.
-
constructor.
Admitted.

Lemma Nth_tl : forall A (l : list A) a n, Nth l (S n) a -> Nth (List.tl l) n a.
Proof using.
Admitted.

Lemma clients_only_move_up_in_queue : forall n c s, lb_step_execution lb_step_async s -> Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c -> weak_until (fun s => Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c) (next (fun s => Nth (queue (nwState (evt_a (hd s)) Server)) n c /\ (n = 0 -> In (mkPacket Server (Client c) Locked) (nwPackets (evt_a (hd s)))))) s.
Proof using.
intros n c.
cofix CIH.
destruct s.
destruct e.
intros Hexec HNth.
invcs Hexec.
invcs H1.
-
unfold runGenHandler, NetHandler in *.
break_match.
+
coinductive_case CIH.
find_rewrite.
simpl.
now rewrite_update.
+
find_apply_lem_hyp ServerNetHandler_lbcases.
intuition.
*
coinductive_case CIH.
repeat find_rewrite.
simpl.
rewrite_update.
break_exists.
intuition; repeat find_rewrite; try solve_by_inversion.
now eauto using Nth_app.
*
exfalso.
clear CIH.
subst.
invcs HNth.
repeat find_reverse_rewrite.
simpl in *.
repeat find_rewrite.
now solve_by_inversion.
*
clear CIH.
apply W0.
simpl.
fold LockServ_MultiParams in *.
repeat find_rewrite.
simpl.
rewrite_update.
repeat find_rewrite.
intuition eauto using Nth_tl.
break_exists.
intuition.
subst.
find_apply_lem_hyp Nth_tl.
repeat find_rewrite.
invcs HNth.
auto.
*
coinductive_case CIH.
repeat find_rewrite.
simpl.
now rewrite_update.
-
unfold runGenHandler in *.
find_apply_lem_hyp InputHandler_cases.
intuition.
+
break_exists.
break_and.
subst.
coinductive_case CIH.
repeat find_rewrite.
simpl.
now rewrite_update.
+
coinductive_case CIH.
repeat find_rewrite.
simpl.
update_destruct; subst; now rewrite_update.
-
Admitted.

Lemma MsgUnlock_moves_client : forall n c s, lb_step_execution lb_step_async s -> Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c -> now (occurred MsgUnlock) s -> next (fun s => Nth (queue (nwState (evt_a (hd s)) Server)) n c /\ (n = 0 -> In (mkPacket Server (Client c) Locked) (nwPackets (evt_a (hd s))))) s.
Proof using.
intros n c s Hexec HNth Hlabel.
destruct s.
simpl.
invcs Hexec.
match goal with | H : lb_step_async _ _ _ _ |- _ => invcs H end.
-
unfold occurred in *.
match goal with | H : MsgUnlock = _ |- _ => symmetry in H; repeat find_rewrite; clear H end.
monad_unfold.
unfold NetHandler in *.
break_match.
+
find_apply_lem_hyp ClientNetHandler_lbcases.
intuition; congruence.
+
find_apply_lem_hyp ServerNetHandler_lbcases.
repeat (break_and; try break_or_hyp); break_exists; repeat (break_and; try break_or_hyp); try congruence.
*
exfalso.
repeat find_rewrite.
invcs HNth.
repeat find_reverse_rewrite.
simpl in *.
subst.
solve_by_inversion.
*
fold LockServ_MultiParams in *.
repeat find_rewrite.
simpl in *.
find_apply_lem_hyp Nth_tl.
repeat find_rewrite.
intuition; [|intros; subst; solve_by_inversion].
rewrite_update.
congruence.
-
unfold occurred in *.
match goal with | H : MsgUnlock = _ |- _ => symmetry in H; repeat find_rewrite; clear H end.
monad_unfold.
find_apply_lem_hyp InputHandler_lbcases.
intuition; break_exists; intuition; congruence.
-
unfold occurred in *.
Admitted.

Lemma Unlock_enables_MsgUnlock : forall n, message_enables_label (mkPacket n Server Unlock) MsgUnlock.
Proof using.
unfold message_enables_label.
intros.
find_apply_lem_hyp in_split.
break_exists_name xs.
break_exists_name ys.
unfold enabled.
destruct (ServerNetHandler n Unlock (nwState net Server)) eqn:?.
destruct p.
destruct p.
cut (l0 = MsgUnlock); intros.
subst.
-
repeat eexists.
econstructor; eauto.
-
handler_unfold.
Admitted.

Lemma Unlock_in_network_eventually_MsgUnlock : forall c s, lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> In (mkPacket c Server Unlock) (nwPackets (evt_a (hd s))) -> eventually (now (occurred MsgUnlock)) s.
Proof using.
intros.
eapply message_labels_eventually_occur; eauto using Unlock_enables_MsgUnlock, Unlock_delivered_MsgUnlock.
unfold label_silent.
simpl.
Admitted.

Lemma Nth_something_at_head : forall A (l : list A) n x, Nth l n x -> exists y l', l = y :: l'.
Proof using.
intros.
Admitted.

Lemma InputUnlock_held : forall s c, lb_step_execution lb_step_async s -> held (nwState (evt_a (hd s)) (Client c)) = true -> now (occurred (InputUnlock c)) s -> next (fun s => In (mkPacket (Client c) Server Unlock) (nwPackets (evt_a (hd s)))) s.
Proof using.
intros.
invcs H.
invcs H2.
-
monad_unfold.
unfold NetHandler in *.
break_match_hyp.
+
unfold occurred in *.
find_apply_lem_hyp ClientNetHandler_lbcases; intuition; congruence.
+
unfold occurred in *.
find_apply_lem_hyp ServerNetHandler_lbcases; intuition; break_exists; intuition; congruence.
-
monad_unfold.
find_apply_lem_hyp InputHandler_lbcases.
intuition; try congruence.
break_exists.
intuition; try congruence.
fold LockServ_MultiParams in *.
repeat find_rewrite.
simpl.
left.
unfold occurred in *.
congruence.
-
unfold occurred in *.
Admitted.

Lemma InputHandler_Client_Unlock : forall c sigma, exists sigma' os ms, InputHandler (Client c) Unlock sigma = (InputUnlock c, os, sigma', ms).
Proof using.
intros.
unfold InputHandler.
unfold ClientIOHandler.
monad_unfold.
repeat break_let.
find_inversion.
Admitted.

Lemma InputUnlock_enabled : forall s c, lb_step_execution lb_step_async s -> now (enabled lb_step_async (InputUnlock c)) s.
Proof using.
intros.
destruct s.
simpl.
unfold enabled, enabled.
pose proof (InputHandler_Client_Unlock c (nwState (evt_a e) (Client c))).
break_exists.
repeat eexists.
unfold InputHandler in *.
unfold ClientIOHandler in *.
Admitted.

Lemma InputUnlock_continuously_enabled : forall s c, lb_step_execution lb_step_async s -> cont_enabled lb_step_async (InputUnlock c) s.
Proof using.
unfold cont_enabled.
intros.
apply always_continuously.
Admitted.

Lemma held_until_Unlock : forall c s, lb_step_execution lb_step_async s -> held (nwState (evt_a (hd s)) (Client c)) = true -> weak_until (fun s => held (nwState (evt_a (hd s)) (Client c)) = true) (next (fun s => In (mkPacket (Client c) Server Unlock) (nwPackets (evt_a (hd s))))) s.
Proof using.
intros c.
cofix CIH.
destruct s.
simpl.
intros.
invcs H.
invcs H3.
-
coinductive_case CIH.
monad_unfold.
unfold NetHandler in *.
break_match_hyp.
+
find_apply_lem_hyp ClientNetHandler_cases.
repeat find_rewrite.
simpl.
intuition; update_destruct_max_simplify; repeat find_rewrite; auto.
+
find_apply_lem_hyp ServerNetHandler_cases.
repeat find_rewrite.
simpl.
intuition; break_exists; intuition; rewrite_update; repeat find_rewrite; auto.
-
monad_unfold.
find_apply_lem_hyp InputHandler_lbcases.
intuition; break_exists; intuition.
+
coinductive_case CIH.
repeat find_rewrite.
simpl.
update_destruct_max_simplify; repeat find_rewrite; auto.
+
subst.
destruct (fin_eq_dec _ c x).
*
clear CIH.
subst.
apply W0; simpl.
fold LockServ_MultiParams in *.
repeat find_rewrite.
simpl.
auto.
*
coinductive_case CIH.
repeat find_rewrite.
simpl.
now rewrite_update.
+
coinductive_case CIH.
clear CIH.
repeat find_rewrite.
simpl.
update_destruct_max_simplify; repeat find_rewrite; auto.
+
coinductive_case CIH.
clear CIH.
repeat find_rewrite.
simpl.
update_destruct_max_simplify; repeat find_rewrite; auto.
-
coinductive_case CIH.
Admitted.

Lemma held_eventually_InputUnlock : forall c s, lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> eventually (now (occurred (InputUnlock c))) s.
Proof using.
intros.
pose proof (@InputUnlock_continuously_enabled s c).
intuition.
eapply_prop_hyp weak_fairness cont_enabled; [|now unfold label_silent].
Admitted.

Lemma held_eventually_Unlock : forall s c, lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> held (nwState (evt_a (hd s)) (Client c)) = true -> eventually (fun s => In (mkPacket (Client c) Server Unlock) (nwPackets (evt_a (hd s)))) s.
Proof using.
intros.
apply eventually_next.
match goal with | H : context [held] |- _ => pattern s in H end.
match goal with | H1 : ?J1 s, H2 : ?J2 s, H3 : ?J3 s |- _ => assert ((J1 /\_ J2 /\_ J3) s) by (now unfold and_tl); eapply weak_until_eventually with (J := (and_tl J1 (and_tl J2 J3))) end; simpl in *.
2:now unfold and_tl.
3:eauto using held_eventually_InputUnlock.
-
intros.
unfold and_tl in *.
intuition.
eapply InputUnlock_held; eauto.
-
apply weak_until_always; eauto using lb_step_execution_invar, always_inv.
apply weak_until_always; eauto using weak_fairness_invar, always_inv.
Admitted.

Lemma Locked_enables_MsgLocked : forall i, message_enables_label {| pSrc := Server; pDst := Client i; pBody := Locked |} (MsgLocked i).
Proof using.
unfold message_enables_label, enabled.
intros.
find_apply_lem_hyp in_split.
break_exists_name xs.
break_exists_name ys.
do 2 eexists.
eapply LabeledStepAsync_deliver; eauto.
simpl.
monad_unfold.
simpl.
Admitted.

Lemma Locked_delivered_MsgLocked : forall i, message_delivered_label {| pSrc := Server; pDst := Client i; pBody := Locked |} (MsgLocked i).
Proof using.
unfold message_delivered_label.
intros.
invcs H.
-
repeat find_rewrite.
find_eapply_lem_hyp In_split_not_In; eauto.
subst.
monad_unfold.
simpl in *.
handler_unfold.
repeat break_match; repeat find_inversion; auto.
-
unfold not in *.
find_false.
apply in_app_iff; auto.
-
Admitted.

Lemma Locked_in_network_eventually_MsgLocked : forall i s, lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> In (mkPacket Server (Client i) Locked) (nwPackets (evt_a (hd s))) -> eventually (now (occurred (MsgLocked i))) s.
Proof using.
intros.
eapply message_labels_eventually_occur; eauto using Locked_enables_MsgLocked, Locked_delivered_MsgLocked.
unfold label_silent.
simpl.
Admitted.

Lemma MsgLocked_held : forall s c, lb_step_execution lb_step_async s -> now (occurred (MsgLocked c)) s -> next (fun s => held (nwState (evt_a (hd s)) (Client c)) = true) s.
Proof using.
intros.
invcs H.
invcs H1.
-
monad_unfold.
unfold NetHandler in *.
break_match_hyp.
+
unfold occurred in *.
fold LockServ_MultiParams in *.
repeat find_rewrite.
simpl.
find_apply_lem_hyp ClientNetHandler_lbcases; intuition; subst; update_destruct_max_simplify; congruence.
+
unfold occurred in *.
find_apply_lem_hyp ServerNetHandler_lbcases; intuition; break_exists; intuition; congruence.
-
monad_unfold.
find_apply_lem_hyp InputHandler_lbcases.
intuition; break_exists; intuition; congruence.
-
Admitted.

Lemma eventually_Unlock : forall n c s, event_step_star step_async step_async_init (hd s) -> lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c -> exists c, eventually (fun s => In (mkPacket c Server Unlock) (nwPackets (evt_a (hd s)))) s.
Proof using.
intros.
find_apply_lem_hyp Nth_something_at_head.
break_exists_name holder.
break_exists.
exists (Client holder).
remember H0 as Hlbs; clear HeqHlbs.
invcs H0.
find_eapply_lem_hyp head_grant_state_unlock; eauto.
intuition.
-
eapply eventually_trans with (inv := lb_step_execution lb_step_async /\_ weak_fairness (lb_step_async(labeled_multi_params := LockServ_LabeledParams)) Silent) (P := now (occurred (MsgLocked holder))).
all:unfold and_tl in *; intuition.
+
eauto using lb_step_execution_invar.
+
eauto using weak_fairness_invar.
+
find_apply_lem_hyp MsgLocked_held; eauto.
destruct s.
simpl in *.
eauto using lb_step_execution_invar, weak_fairness_invar, E_next, held_eventually_Unlock.
+
apply Locked_in_network_eventually_MsgLocked; auto.
-
eauto using held_eventually_Unlock.
-
Admitted.

Lemma eventually_MsgUnlock : forall n c s, event_step_star step_async step_async_init (hd s) -> lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c -> eventually (now (occurred MsgUnlock)) s.
Proof using.
intros n c s Hstar Hexec Hfair HNth.
pattern s in Hexec.
pattern s in Hfair.
find_copy_eapply_lem_hyp eventually_Unlock; eauto.
break_exists.
match goal with | H1 : (fun x => ?J1) s, H2 : (fun x => ?J2) s |- _ => assert (and_tl (fun x => J1) (fun x => J2) s) as Hand by (now unfold and_tl); clear H1; clear H2 end; simpl in *.
eapply eventually_trans.
4:eauto.
3:apply Hand.
2:intros; eapply Unlock_in_network_eventually_MsgUnlock.
all:unfold and_tl in *; intuition eauto.
-
eauto using lb_step_execution_invar.
-
simpl.
Admitted.

Lemma clients_move_up_in_queue : forall n c s, event_step_star step_async step_async_init (hd s) -> lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c -> eventually (fun s => Nth (queue (nwState (evt_a (hd s)) Server)) n c /\ (n = 0 -> In (mkPacket Server (Client c) Locked) (nwPackets (evt_a (hd s))))) s.
Proof using.
intros n c s Hstar Hexec Hfair HNth.
apply eventually_next.
pattern s in HNth.
match goal with | H1 : ?J1 s, H2 : ?J2 s, H3 : ?J3 s |- _ => assert ((J1 /\_ J2 /\_ J3) s) by (now unfold and_tl); eapply weak_until_eventually with (J := (and_tl J1 (and_tl J2 J3))) end; simpl in *.
2:now unfold and_tl.
3:eauto using eventually_MsgUnlock.
-
intros.
unfold and_tl in *.
intuition.
eapply MsgUnlock_moves_client; eauto.
-
apply weak_until_always; eauto using lb_step_execution_invar, always_inv.
apply weak_until_always; eauto using weak_fairness_invar, always_inv.
Admitted.

Lemma clients_move_way_up_in_queue : forall n n' c s, n' <= n -> event_step_star step_async step_async_init (hd s) -> lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> (Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c /\ (S n = 0 -> In (mkPacket Server (Client c) Locked) (nwPackets (evt_a (hd s))))) -> eventually (fun s => Nth (queue (nwState (evt_a (hd s)) Server)) n' c /\ (n' = 0 -> In (mkPacket Server (Client c) Locked) (nwPackets (evt_a (hd s))))) s.
Proof using.
induction n; intros; simpl in *; auto.
-
intuition.
assert (n' = 0) by omega.
subst.
eauto using clients_move_up_in_queue.
-
match goal with | H : _ (hd s) |- _ => pattern s in H end.
match goal with | H1 : ?J1 s, H2 : ?J2 s, H3 : ?J3 s |- _ => assert ((J1 /\_ J2 /\_ J3) s) as Hand by (now unfold and_tl); clear H1; clear H2; clear H3 end; simpl in *.
find_apply_lem_hyp le_lt_eq_dec.
intuition.
+
assert (n' <= n) by omega.
find_eapply_lem_hyp clients_move_up_in_queue; eauto; try solve [unfold and_tl in *; intuition]; [idtac].
eapply eventually_trans.
4:eauto.
3:apply Hand.
all:unfold and_tl in *.
all:intuition eauto using lb_step_execution_invar, weak_fairness_invar.
find_apply_lem_hyp step_async_star_lb_step_execution; auto.
destruct s0.
simpl in *.
find_apply_lem_hyp always_Cons.
intuition.
find_apply_lem_hyp always_Cons.
intuition.
+
subst.
unfold and_tl in *.
intuition.
Admitted.

Lemma clients_get_lock_messages : forall n c s, event_step_star step_async step_async_init (hd s) -> lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> Nth (queue (nwState (evt_a (hd s)) Server)) (S n) c -> eventually (fun s => In (mkPacket Server (Client c) Locked) (nwPackets (evt_a (hd s)))) s.
Proof using.
intros.
pose proof (@clients_move_way_up_in_queue n 0 c s).
pose proof (Nat.le_0_l n).
repeat concludes.
conclude_using ltac:(intuition; congruence).
eapply eventually_monotonic_simple; [|eauto].
intros.
simpl in *.
Admitted.

Lemma InputLock_Lock : forall s c, lb_step_execution lb_step_async s -> now (occurred (InputLock c)) s -> next (fun s => In (mkPacket (Client c) Server Lock) (nwPackets (evt_a (hd s)))) s.
Proof using.
intros.
invcs H.
invcs H1.
-
monad_unfold.
unfold NetHandler in *.
break_match_hyp.
+
unfold occurred in *.
find_apply_lem_hyp ClientNetHandler_lbcases; intuition; congruence.
+
unfold occurred in *.
find_apply_lem_hyp ServerNetHandler_lbcases; intuition; break_exists; intuition; congruence.
-
monad_unfold.
find_apply_lem_hyp InputHandler_lbcases.
intuition; try congruence.
break_exists.
intuition; try congruence.
fold LockServ_MultiParams in *.
repeat find_rewrite.
simpl.
left.
unfold occurred in *.
congruence.
-
unfold occurred in *.
Admitted.

Lemma Lock_in_network_eventually_MsgLock : forall c s, lb_step_execution lb_step_async s -> weak_fairness lb_step_async label_silent s -> In (mkPacket (Client c) Server Lock) (nwPackets (evt_a (hd s))) -> eventually (now (occurred (MsgLock c))) s.
Proof using.
intros.
eapply message_labels_eventually_occur; eauto using Lock_enables_MsgLock, Lock_delivered_MsgLock.
unfold label_silent.
simpl.
Admitted.

Lemma Unlock_delivered_MsgUnlock : forall n, message_delivered_label (mkPacket n Server Unlock) MsgUnlock.
Proof using.
unfold message_delivered_label.
intros.
invcs H.
-
repeat find_rewrite.
find_eapply_lem_hyp In_split_not_In; eauto.
subst.
monad_unfold.
simpl in *.
handler_unfold.
repeat break_match; repeat find_inversion; auto.
-
unfold not in *.
find_false.
apply in_app_iff; auto.
-
intuition.
