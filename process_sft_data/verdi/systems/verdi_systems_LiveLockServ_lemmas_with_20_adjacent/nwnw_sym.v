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

Definition Name_eq_dec : forall a b : Name, {a = b} + {a <> b}.
decide equality.
Admitted.

Definition Msg_eq_dec : forall a b : Msg, {a = b} + {a <> b}.
Admitted.

Theorem In_n_Nodes : forall n : Name, In n Nodes.
Proof using.
intros.
unfold Nodes, list_Clients.
simpl.
destruct n.
-
right.
apply in_map.
apply all_fin_all.
-
left.
Admitted.

Theorem nodup : NoDup Nodes.
Proof using.
unfold Nodes, list_Clients.
apply NoDup_cons.
-
in_crush.
discriminate.
-
apply NoDup_map_injective.
+
intros.
congruence.
+
Admitted.

Lemma locks_correct_implies_mutex : forall sigma, locks_correct sigma -> mutual_exclusion sigma.
Proof using.
unfold locks_correct, mutual_exclusion.
intros.
repeat find_apply_hyp_hyp.
break_exists.
find_rewrite.
find_inversion.
Admitted.

Lemma locks_correct_init : locks_correct init_handlers.
Proof using.
unfold locks_correct.
simpl.
Admitted.

Lemma InputHandler_cases : forall h i st u out st' ms, InputHandler h i st = (u, out, st', ms) -> (exists c, h = Client c /\ ((i = Lock /\ out = [] /\ st' = st /\ ms = [(Server, Lock)]) \/ (i = Unlock /\ out = [] /\ held st' = false /\ ((held st = true /\ ms = [(Server, Unlock)]) \/ (st' = st /\ ms = []))))) \/ (out = [] /\ st' = st /\ ms = []).
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

Lemma locks_correct_update_false : forall sigma st' x, locks_correct sigma -> held st' = false -> locks_correct (update name_eq_dec sigma (Client x) st').
Proof using.
unfold locks_correct.
intuition.
destruct (Name_eq_dec (Client x) (Client n)).
-
find_inversion.
exfalso.
rewrite_update.
congruence.
-
rewrite_update.
Admitted.

Lemma locks_correct_input_handlers : forall h i sigma u st' out ms, InputHandler h i (sigma h) = (u, out, st', ms) -> locks_correct sigma -> locks_correct (update name_eq_dec sigma h st').
Proof using.
Admitted.

Lemma ClientNetHandler_cases : forall c m st u out st' ms, ClientNetHandler c m st = (u, out, st', ms) -> ms = [] /\ ((st' = st /\ out = [] /\ m <> Locked) \/ (m = Locked /\ out = [Locked] /\ held st' = true)).
Proof using.
handler_unfold.
intros.
Admitted.

Lemma ServerNetHandler_cases : forall src m st u out st' ms, ServerNetHandler src m st = (u, out, st', ms) -> out = [] /\ ((exists c, src = Client c /\ (m = Lock /\ queue st' = queue st ++ [c] /\ ((queue st = [] /\ ms = [(Client c, Locked)]) \/ (queue st <> [] /\ ms = [])))) \/ ((m = Unlock /\ queue st' = tail (queue st) /\ ((queue st' = [] /\ ms = []) \/ (exists next t, queue st' = next :: t /\ ms = [(Client next, Locked)])))) \/ ms = [] /\ st' = st /\ m <> Unlock).
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
intuition (auto; congruence).
-
simpl.
destruct st; simpl in *; subst; intuition (auto; congruence).
-
simpl in *.
intuition.
-
simpl in *.
intuition eauto.
-
simpl.
Admitted.

Lemma at_head_of_queue_intro : forall sigma c t, queue (sigma Server) = c :: t -> at_head_of_queue sigma c.
Proof using.
unfold at_head_of_queue.
Admitted.

Lemma locks_correct_update_true : forall sigma c st', held st' = true -> at_head_of_queue sigma c -> locks_correct sigma -> locks_correct (update name_eq_dec sigma (Client c) st').
Proof using.
unfold locks_correct.
intros.
Admitted.

Lemma locks_correct_locked_at_head : forall sigma p c, pDst p = Client c -> pBody p = Locked -> locks_correct_locked sigma p -> at_head_of_queue sigma c.
Proof using.
unfold locks_correct_locked.
firstorder.
repeat find_rewrite.
find_inversion.
Admitted.

Lemma all_clients_false_locks_correct_server_update : forall sigma st, (forall c, held (sigma (Client c)) = false) -> locks_correct (update name_eq_dec sigma Server st).
Proof using.
unfold locks_correct.
intros.
rewrite_update.
Admitted.

Lemma locks_correct_true_at_head_of_queue : forall sigma x, locks_correct sigma -> held (sigma (Client x)) = true -> at_head_of_queue sigma x.
Proof using.
unfold locks_correct.
intros.
find_apply_hyp_hyp.
break_exists.
Admitted.

Lemma at_head_of_nil : forall sigma c, at_head_of_queue sigma c -> queue (sigma Server) = [] -> False.
Proof using.
unfold at_head_of_queue.
firstorder.
Admitted.

Lemma empty_queue_all_clients_false : forall sigma, locks_correct sigma -> queue (sigma Server) = [] -> (forall c, held (sigma (Client c)) = false).
Proof using.
intuition.
destruct (held (sigma (Client c))) eqn:?; auto.
exfalso.
Admitted.

Lemma unlock_in_flight_all_clients_false : forall sigma p, pBody p = Unlock -> locks_correct_unlock sigma p -> locks_correct sigma -> (forall c, held (sigma (Client c)) = false).
Proof using.
intros.
destruct (held (sigma (Client c))) eqn:?; auto.
firstorder.
find_copy_apply_lem_hyp locks_correct_true_at_head_of_queue; auto.
unfold at_head_of_queue in *.
break_exists.
Admitted.

Lemma locks_correct_at_head_preserved : forall sigma st', locks_correct sigma -> (forall c, at_head_of_queue sigma c -> at_head_of_queue (update name_eq_dec sigma Server st') c) -> locks_correct (update name_eq_dec sigma Server st').
Proof using.
unfold locks_correct, at_head_of_queue.
firstorder.
rewrite_update.
Admitted.

Lemma snoc_at_head_of_queue_preserved : forall sigma st' x, queue st' = queue (sigma Server) ++ [x] -> (forall c, at_head_of_queue sigma c -> at_head_of_queue (update name_eq_dec sigma Server st') c).
Proof using.
unfold at_head_of_queue.
intuition.
break_exists.
rewrite_update.
find_rewrite.
Admitted.

Lemma locks_correct_net_handlers : forall p sigma u st' out ms, NetHandler (pDst p) (pSrc p) (pBody p) (sigma (pDst p)) = (u, out, st', ms) -> locks_correct sigma -> locks_correct_unlock sigma p -> locks_correct_locked sigma p -> locks_correct (update name_eq_dec sigma (pDst p) st').
Proof using.
Admitted.

Lemma locks_correct_unlock_sent_lock : forall sigma p, pBody p = Lock -> locks_correct_unlock sigma p.
Proof using.
unfold locks_correct_unlock.
intuition.
Admitted.

Lemma locks_correct_unlock_sent_locked : forall sigma p, pBody p = Locked -> locks_correct_unlock sigma p.
Proof using.
unfold locks_correct_unlock.
intuition.
Admitted.

Lemma locks_correct_unlock_input_handlers_old : forall h i sigma u st' out ms p, InputHandler h i (sigma h) = (u, out, st', ms) -> locks_correct sigma -> locks_correct_unlock sigma p -> locks_correct_unlock (update name_eq_dec sigma h st') p.
Proof using.
set_up_input_handlers.
destruct (pBody p) eqn:?.
-
auto using locks_correct_unlock_sent_lock.
-
now erewrite unlock_in_flight_all_clients_false in * by eauto.
-
Admitted.

Lemma nwnw_sym : forall p q, LockServ_network_network_invariant p q -> LockServ_network_network_invariant q p.
Proof using.
unfold LockServ_network_network_invariant.
intuition.
