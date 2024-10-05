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

Lemma trace_mutex'_no_out_extend : forall tr n h, trace_mutual_exclusion' h tr -> trace_mutual_exclusion' h (tr ++ [(n, inr [])]).
Proof using.
Admitted.

Lemma last_holder'_no_out_inv : forall tr h c n, last_holder' h (tr ++ [(c, inr [])]) = Some n -> last_holder' h tr = Some n.
Proof using.
Admitted.

Lemma last_holder'_no_out_extend : forall tr h c n, last_holder' h tr = Some n -> last_holder' h (tr ++ [(c, inr [])]) = Some n.
Proof using.
Admitted.

Lemma decomposition_reachable_nw_invariant : forall st tr p, step_async_star step_async_init st tr -> In p (nwPackets st) -> network_invariant (nwState st) p.
Proof using.
pose proof decomposition_invariant.
find_apply_lem_hyp inductive_invariant_true_in_reachable.
unfold true_in_reachable, reachable in *.
intuition.
unfold composed_invariant in *.
Admitted.

Lemma trace_mutex'_locked_extend : forall tr h n, trace_mutual_exclusion' h tr -> last_holder' h tr = None -> trace_mutual_exclusion' h (tr ++ [(Client n, inr [Locked])]).
Proof using.
induction tr; intros; simpl in *.
-
subst.
auto.
-
simpl in *.
Admitted.

Lemma reachable_intro : forall a tr, step_async_star step_async_init a tr -> reachable step_async step_async_init a.
Proof using.
unfold reachable.
intros.
Admitted.

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

Lemma last_holder'_input_extend : forall tr h c i n, i <> Unlock -> last_holder' h tr = Some n -> last_holder' h (tr ++ [(Client c, inl i)]) = Some n.
Proof using.
induction tr; intros; simpl in *; repeat break_match; auto.
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

Lemma last_holder'_server_extend : forall tr h i, last_holder' h (tr ++ [(Server, inl i)]) = last_holder' h tr.
Proof using.
induction tr; intros; simpl in *; repeat break_match; auto.
