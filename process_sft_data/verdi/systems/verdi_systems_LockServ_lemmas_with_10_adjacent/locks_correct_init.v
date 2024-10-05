Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Require Import StructTact.Fin.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Require Import Verdi.StatePacketPacketDecomposition.
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
Definition Handler (S : Type) := GenHandler (Name * Msg) S Output unit.
Definition ClientNetHandler (i : Client_index) (m : Msg) : Handler Data := match m with | Locked => (put (mkData [] true)) >> write_output Locked | _ => nop end.
Definition ClientIOHandler (i : Client_index) (m : Msg) : Handler Data := match m with | Lock => send (Server, Lock) | Unlock => data <- get ;; when (held data) (put (mkData [] false) >> send (Server, Unlock)) | _ => nop end.
Definition ServerNetHandler (src : Name) (m : Msg) : Handler Data := st <- get ;; let q := queue st in match m with | Lock => match src with | Server => nop | Client c => when (null q) (send (src, Locked)) >> put (mkData (q++[c]) (held st)) end | Unlock => match q with | _ :: x :: xs => put (mkData (x :: xs) (held st)) >> send (Client x, Locked) | _ => put (mkData [] (held st)) end | _ => nop end.
Definition ServerIOHandler (m : Msg) : Handler Data := nop.
Definition NetHandler (nm src : Name) (m : Msg) : Handler Data := match nm with | Client c => ClientNetHandler c m | Server => ServerNetHandler src m end.
Definition InputHandler (nm : Name) (m : Msg) : Handler Data := match nm with | Client c => ClientIOHandler c m | Server => ServerIOHandler m end.
Ltac handler_unfold := repeat (monad_unfold; unfold NetHandler, InputHandler, ServerNetHandler, ClientNetHandler, ClientIOHandler, ServerIOHandler in *).
Definition Nodes := Server :: list_Clients.
Global Instance LockServ_BaseParams : BaseParams := { data := Data ; input := Input ; output := Output }.
Global Instance LockServ_MultiParams : MultiParams LockServ_BaseParams := { name := Name ; msg := Msg ; msg_eq_dec := Msg_eq_dec ; name_eq_dec := Name_eq_dec ; nodes := Nodes ; all_names_nodes := In_n_Nodes ; no_dup_nodes := nodup ; init_handlers := init_data ; net_handlers := fun dst src msg s => runGenHandler_ignore s (NetHandler dst src msg) ; input_handlers := fun nm msg s => runGenHandler_ignore s (InputHandler nm msg) }.
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
Instance LockServ_Decompositition : Decomposition _ LockServ_MultiParams.
apply Build_Decomposition with (state_invariant := locks_correct) (network_invariant := LockServ_network_invariant) (network_network_invariant := LockServ_network_network_invariant); simpl; intros; monad_unfold; repeat break_let; repeat find_inversion.
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

Lemma nwnw_sym : forall p q, LockServ_network_network_invariant p q -> LockServ_network_network_invariant q p.
Proof using.
unfold LockServ_network_network_invariant.
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

Lemma ClientNetHandler_cases : forall c m st u out st' ms, ClientNetHandler c m st = (u, out, st', ms) -> ms = [] /\ ((st' = st /\ out = [] ) \/ (m = Locked /\ out = [Locked] /\ held st' = true)).
Proof using.
handler_unfold.
intros.
Admitted.

Lemma ServerNetHandler_cases : forall src m st u out st' ms, ServerNetHandler src m st = (u, out, st', ms) -> out = [] /\ ((exists c, src = Client c /\ (m = Lock /\ queue st' = queue st ++ [c] /\ ((queue st = [] /\ ms = [(Client c, Locked)]) \/ (queue st <> [] /\ ms = [])))) \/ ((m = Unlock /\ queue st' = tail (queue st) /\ ((queue st' = [] /\ ms = []) \/ (exists next t, queue st' = next :: t /\ ms = [(Client next, Locked)])))) \/ ms = [] /\ st' = st).
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
auto.
-
simpl.
destruct st; simpl in *; subst; auto.
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

Lemma locks_correct_init : locks_correct init_handlers.
Proof using.
unfold locks_correct.
simpl.
discriminate.
