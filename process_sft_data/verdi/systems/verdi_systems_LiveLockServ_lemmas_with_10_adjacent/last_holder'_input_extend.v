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

Lemma locks_correct_locked_invariant : forall st p, reachable step_async step_async_init st -> In p (nwPackets st) -> locks_correct_locked (nwState st) p.
Proof using.
intros.
pose proof decomposition_invariant.
find_apply_lem_hyp inductive_invariant_true_in_reachable.
unfold true_in_reachable in *.
Admitted.

Lemma locks_correct_invariant : forall st, reachable step_async step_async_init st -> locks_correct (nwState st).
Proof using.
intros.
pose proof decomposition_invariant.
find_apply_lem_hyp inductive_invariant_true_in_reachable.
unfold true_in_reachable in *.
Admitted.

Lemma mutual_exclusion_invariant : forall st, reachable step_async step_async_init st -> mutual_exclusion (nwState st).
Proof using.
intros.
apply locks_correct_implies_mutex.
Admitted.

Lemma last_holder'_locked_some_eq : forall tr h c n, last_holder' h (tr ++ [(Client c, inr [Locked])]) = Some n -> c = n.
Proof using.
induction tr; intros; simpl in *; repeat break_match; subst; eauto.
Admitted.

Lemma last_holder'_server_extend : forall tr h i, last_holder' h (tr ++ [(Server, inl i)]) = last_holder' h tr.
Proof using.
Admitted.

Lemma last_holder'_locked_extend : forall tr h n, last_holder' h (tr ++ [(Client n, inr [Locked])]) = Some n.
Proof using.
Admitted.

Lemma trace_mutual_exclusion'_extend_input : forall tr h c i, i <> Unlock -> trace_mutual_exclusion' h tr -> trace_mutual_exclusion' h (tr ++ [(Client c, inl i)]).
Proof using.
Admitted.

Lemma trace_mutual_exclusion'_extend_input_server : forall tr h i, trace_mutual_exclusion' h tr -> trace_mutual_exclusion' h (tr ++ [(Server, inl i)]).
Proof using.
Admitted.

Lemma last_holder'_input_inv : forall tr h c i n, i <> Unlock -> last_holder' h (tr ++ [(Client c, inl i)]) = Some n -> last_holder' h tr = Some n.
Proof using.
Admitted.

Lemma last_holder'_input_inv_server : forall tr h i n, last_holder' h (tr ++ [(Server, inl i)]) = Some n -> last_holder' h tr = Some n.
Proof using.
Admitted.

Lemma trace_mutex'_unlock_extend : forall tr h c, trace_mutual_exclusion' h tr -> trace_mutual_exclusion' h (tr ++ [(Client c, inl Unlock)]).
Proof using.
Admitted.

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

Lemma last_holder'_input_extend : forall tr h c i n, i <> Unlock -> last_holder' h tr = Some n -> last_holder' h (tr ++ [(Client c, inl i)]) = Some n.
Proof using.
induction tr; intros; simpl in *; repeat break_match; auto.
congruence.
