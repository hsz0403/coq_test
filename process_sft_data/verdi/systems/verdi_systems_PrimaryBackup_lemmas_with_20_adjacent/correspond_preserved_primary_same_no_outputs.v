Require Import Verdi.Verdi.
Require Import Verdi.HandlerMonad.
Local Arguments update {_} {_} _ _ _ _ _ : simpl never.
Class PrimaryBackupParams (base_params : BaseParams) := { input_eq_dec : forall x y : input, {x = y} + {x <> y} }.
Section PrimaryBackup.
Context {base_params : BaseParams}.
Context {one_node_params : OneNodeParams base_params}.
Context {pb_params : PrimaryBackupParams base_params}.
Inductive name := Primary | Backup.
Inductive msg := | BackItUp : input -> msg | Ack : msg.
Inductive PB_input := | Request : input -> PB_input | Read : PB_input.
Inductive PB_output := | RequestResponse : input -> output -> PB_output | ReadResponse : data -> PB_output.
Record PB_data := { queue : list input; state : data }.
Definition all_nodes : list name := [Primary; Backup].
Definition PB_init (n : name) := Build_PB_data [] init.
Definition set_queue {W O} (l : list input) := modify (W := W)(O := O) (fun d => Build_PB_data l (state d)).
Definition set_state {W O} (st : data) := modify (W := W)(O := O) (fun d => Build_PB_data (queue d) st).
Ltac pb_unfold := unfold set_queue, set_state in *; monad_unfold.
Definition PB_input_handler (h : name) (i : PB_input) (d : PB_data) : list PB_output * PB_data * list (name * msg) := runGenHandler_ignore d ( match h, i with | Primary, Request r => d <- get ;; when (null (queue d)) (send (Backup, BackItUp r)) ;; set_queue (queue d ++ [r]) | _, Read => d <- get ;; write_output (ReadResponse (state d)) | _, _ => nop end).
Definition PB_net (dst src : name) (m : msg) : PB_data -> list PB_output * PB_data * list (name * msg) := fun x => runGenHandler_ignore x ( match dst, m with | Primary, Ack => d <- get ;; match queue d with | [] => nop | x :: xs => match xs with | [] => nop | y :: ys => send (Backup, BackItUp y) end ;; let (os, st') := handler x (state d) in write_output (RequestResponse x os) ;; set_state st' ;; set_queue xs end | Backup, BackItUp i => d <- get ;; set_state (snd (handler i (state d))) ;; send (Primary, Ack) | _, _ => nop end).
Instance PB_base_params : BaseParams := Build_BaseParams PB_data PB_input PB_output.
Instance PB_multi_params : MultiParams PB_base_params := Build_MultiParams PB_base_params msg_eq_dec name_eq_dec all_nodes_all NoDup_all_nodes PB_init PB_net PB_input_handler.
Definition inputs_1 (tr : list ((@input base_params) * (@output base_params))) : list (@input base_params) := map (@fst _ _) tr.
Definition inputs_m (tr : list (name * (@input PB_base_params + list (@output PB_base_params)))) : list (@input base_params) := filterMap (fun x => match x with | (Primary, inl (Request i)) => Some i | _ => None end) tr.
Definition outputs_1 (tr : list ((@input base_params) * (@output base_params))) : list (@output base_params) := map (@snd _ _) tr.
Fixpoint outputs_m (tr : list (name * (@input PB_base_params + list (@output PB_base_params)))) : list (@output base_params) := match tr with | [] => [] | (Primary, inr l) :: tr' => filterMap (fun x => match x with | RequestResponse i os => Some os | _ => None end) l ++ outputs_m tr' | _ :: tr' => outputs_m tr' end.
Fixpoint processInputs (d : @data base_params) (l : list (@input base_params)) : (@data base_params * list (@output base_params)) := match l with | [] => (d, []) | i :: l' => let (os, d') := @handler _ one_node_params i d in let (d'', os') := processInputs d' l' in (d'', os :: os') end.
Definition correspond (st : @data base_params) (sigma : name -> @data PB_base_params) tr_1 tr_m := let (d, os) := processInputs (state (sigma Primary)) (queue (sigma Primary)) in outputs_m tr_m ++ os = outputs_1 tr_1 /\ d = st.
Hint Extern 4 => congruence : core.
Definition network_invariant (net : @network _ PB_multi_params) : Prop := (nwPackets net = [] /\ state (nwState net Primary) = state (nwState net Backup)) \/ (exists i is, nwPackets net = [mkPacket Primary Backup (BackItUp i)] /\ queue (nwState net Primary) = i :: is /\ state (nwState net Primary) = state (nwState net Backup)) \/ (nwPackets net = [mkPacket Backup Primary Ack] /\ exists i is, queue (nwState net Primary) = i :: is /\ snd (handler i (state (nwState net Primary))) = state (nwState net Backup)).
Ltac prep := subst; simpl in *; try find_inversion; repeat find_rewrite; simpl in *.
Ltac workhorse := repeat (prep; match goal with | [ H : _ /\ _ |- _ ] => break_and | [ H : exists _, _ |- _ ] => break_exists | [ H : _ ++ _ :: _ = [] |- _ ] => solve [exfalso; eapply app_cons_not_nil; eauto] | [ H : _ ++ _ :: _ = [ _ ] |- _ ] => apply app_cons_singleton_inv in H | [ H : context [ let (_,_) := ?X in _ ] |- _ ] => destruct X eqn:? | [ |- context [ let (_,_) := ?X in _ ] ] => destruct X eqn:? | [ |- context [ update _ (nwState ?net) ?x (nwState ?net ?x) _ ] ] => rewrite update_nop | [ |- context [ update _ _ ?x _ ?x ] ] => rewrite update_eq by auto | [ |- context [ update _ _ ?x _ ?y ] ] => rewrite update_diff by auto | [ H : _ \/ _ |- _ ] => invc H end); prep.
Fixpoint revert_trace (tr : list (name * ((@input PB_base_params) + list (@output PB_base_params)))) : list (@input base_params * (@output base_params)) := match tr with | [] => [] | (h, t) :: tr' => match t with | inr l => filterMap (fun x => match x with | RequestResponse i os => Some (i, os) | _ => None end) l | _ => [] end ++ revert_trace tr' end.
Definition revert_state (net : network) : @data base_params := state (nwState net Primary).
Definition no_output_at_backup {A} x := forall y, snd x = @inr A _ y -> fst x = Primary \/ match y with | [] => True | [ReadResponse _] => True | _ => False end.
Definition no_output_at_backup_trace {A} tr := (forall x, In x tr -> @no_output_at_backup A x).
Definition zero_or_one_outputs_per_step {A B C} t := forall y, @snd A _ t = @inr B _ y -> y = [] \/ exists z : C, y = [z].
Definition zero_or_one_outputs_per_step_trace {A B C} tr := forall x, In x tr -> @zero_or_one_outputs_per_step A B C x.
End PrimaryBackup.

Lemma name_eq_dec : forall x y : name, {x = y} + {x <> y}.
Proof using.
Admitted.

Lemma msg_eq_dec : forall x y : msg, {x = y} + {x <> y}.
Proof using pb_params.
decide equality.
Admitted.

Lemma all_nodes_all : forall x, In x all_nodes.
Proof using.
unfold all_nodes.
Admitted.

Lemma NoDup_all_nodes : NoDup all_nodes.
Proof using.
unfold all_nodes.
repeat constructor; intuition.
simpl in *.
intuition.
Admitted.

Lemma PB_input_handler_defn : forall h i d os d' ms, PB_input_handler h i d = (os, d', ms) -> (h = Primary /\ state d' = state d /\ os = [] /\ exists r, i = Request r /\ queue d' = queue d ++ [r] /\ (ms = [] \/ (ms = [(Backup, BackItUp r)] /\ queue d = []))) \/ (i = Read /\ d = d' /\ os = [ReadResponse (state d)] /\ ms = []) \/ (h = Backup /\ d = d' /\ ms = [] /\ os = []).
Proof using.
unfold PB_input_handler.
intros.
pb_unfold.
repeat break_match; repeat find_inversion; intuition eauto.
rewrite app_nil_r.
simpl.
find_apply_lem_hyp null_sound.
find_rewrite.
simpl.
left.
intuition.
eexists.
Admitted.

Lemma PB_net_defn : forall dst src m d os d' ms, PB_net dst src m d = (os, d', ms) -> (os = [] /\ d' = d /\ ms = []) \/ (dst = Primary /\ m = Ack /\ ( (queue d = [] /\ os = [] /\ ms = [] /\ d' = d) \/ (exists h t, queue d = h :: t /\ queue d' = t /\ ((t = [] /\ ms = []) \/ (exists y ys, t = y :: ys /\ ms = [(Backup, BackItUp y)])) /\ let (us, st') := handler h (state d) in os = [RequestResponse h us] /\ state d' = st'))) \/ (dst = Backup /\ ms = [(Primary, Ack)] /\ queue d' = queue d /\ os = [] /\ (exists i, m = BackItUp i /\ state d' = snd (handler i (state d)))).
Proof using.
unfold PB_net.
intros.
pb_unfold.
repeat (first [break_let | break_match]); repeat find_inversion; auto.
-
right.
left.
intuition.
right.
eexists.
eexists.
intuition eauto.
find_rewrite.
auto.
-
right.
left.
intuition.
right.
eexists.
eexists.
intuition eauto.
find_rewrite.
auto.
-
right.
right.
intuition.
eexists.
Admitted.

Lemma PB_net_defn' : forall dst src m d os d' ms, PB_net dst src m d = (os, d', ms) -> (os = [] /\ d' = d /\ ms = [] /\ ((dst = Primary /\ exists i, m = BackItUp i) \/ (dst = Backup /\ m = Ack))) \/ (dst = Primary /\ m = Ack /\ ( (queue d = [] /\ os = [] /\ ms = [] /\ d' = d) \/ (exists h t, queue d = h :: t /\ queue d' = t /\ ((t = [] /\ ms = []) \/ (exists y ys, t = y :: ys /\ ms = [(Backup, BackItUp y)])) /\ let (us, st') := handler h (state d) in os = [RequestResponse h us] /\ state d' = st'))) \/ (dst = Backup /\ ms = [(Primary, Ack)] /\ queue d' = queue d /\ os = [] /\ (exists i, m = BackItUp i /\ state d' = snd (handler i (state d)))).
Proof using.
unfold PB_net.
intros.
pb_unfold.
repeat (first [break_let | break_match]); repeat find_inversion; auto; simpl.
-
left.
intuition.
left.
eauto.
-
right.
left.
intuition.
-
right.
left.
intuition.
right.
eexists.
eexists.
intuition eauto.
find_rewrite.
auto.
-
right.
left.
intuition.
right.
eexists.
eexists.
intuition eauto.
find_rewrite.
auto.
-
right.
right.
intuition.
eauto.
-
left.
Admitted.

Lemma inputs_1_nil_outputs_1_nil : forall tr, inputs_1 tr = [] -> outputs_1 tr = [].
Proof using.
destruct tr; auto.
intros.
simpl in *.
Admitted.

Lemma inputs_m_app : forall l1 l2, inputs_m (l1 ++ l2) = inputs_m l1 ++ inputs_m l2.
Proof using.
unfold inputs_m.
intros.
Admitted.

Lemma inputs_m_inr : forall h t tr, inputs_m ((h, inr t) :: tr) = inputs_m tr.
Proof using.
unfold inputs_m.
intros.
simpl.
Admitted.

Lemma PB_net_out_case : forall dst src m d os d' ms, PB_net dst src m d = (os, d', ms) -> (dst = Backup /\ os = [] /\ queue d' = queue d) \/ (dst = Primary /\ os = [] /\ d' = d) \/ (dst = Primary /\ exists h t, queue d = h :: t /\ queue d' = t /\ (let (us, st') := handler h (state d) in os = [RequestResponse h us] /\ state d' = st')).
Proof using.
intros.
find_apply_lem_hyp PB_net_defn.
intuition.
-
destruct dst; subst; intuition.
-
subst.
right.
right.
intuition.
break_exists.
Admitted.

Lemma outputs_m_app : forall tr1 tr2, outputs_m (tr1 ++ tr2) = outputs_m tr1 ++ outputs_m tr2.
Proof using.
intros.
induction tr1; simpl.
-
auto.
-
repeat break_match; subst; auto.
rewrite app_ass.
Admitted.

Lemma outputs_m_inr_nil : forall h l, outputs_m ((h,inr []) :: l) = outputs_m l.
Proof using.
Admitted.

Lemma outputs_m_inr_nil_singleton : forall h, outputs_m [(h,inr [])] = [].
Proof using.
intros.
Admitted.

Lemma outputs_m_inl_read_singleton : forall h, outputs_m [(h, inl Read)] = [].
Proof using.
Admitted.

Lemma outputs_m_inr_primary_singleton : forall h i l, h = Primary -> outputs_m [(h, inr [RequestResponse i l])] = [l].
Proof using.
unfold outputs_m.
intros.
Admitted.

Lemma correspond_preserved_primary_apply_entry : forall sigma sigma' st tr_1 tr_m tr_m' i l d h, correspond st sigma tr_1 tr_m -> handler i (state (sigma h)) = (l, state d) -> sigma' Primary = d -> outputs_m tr_m' = [l] -> h = Primary -> queue (sigma h) = i :: queue d -> correspond st sigma' tr_1 (tr_m ++ tr_m').
Proof using.
unfold correspond.
intros.
subst.
rewrite outputs_m_app.
repeat find_rewrite.
simpl in *.
repeat break_match.
repeat find_inversion.
find_rewrite.
find_inversion.
rewrite app_ass.
Admitted.

Lemma inputs_m_inr_singleton : forall h l, inputs_m [(h, inr l)] = [].
Proof using.
intros.
rewrite inputs_m_inr.
Admitted.

Lemma inputs_m_app_inr_singleton : forall tr h l, inputs_m (tr ++ [(h, inr l)]) = inputs_m tr.
Proof using.
intros.
rewrite inputs_m_app in *.
rewrite inputs_m_inr_singleton in *.
rewrite app_nil_r in *.
Admitted.

Lemma inputs_m_primary_inl : forall i l, inputs_m ((Primary, inl (Request i)) :: l) = i :: inputs_m l.
Proof using.
Admitted.

Lemma inputs_m_primary_inl_request_singleton : forall i, inputs_m [(Primary, inl (Request i))] = [i].
Proof using.
Admitted.

Lemma inputs_m_inl_read_singleton : forall h, inputs_m [(h, inl Read)] = [].
Proof using.
intros.
Admitted.

Lemma inputs_m_inl_read : forall h l, inputs_m ((h, inl Read) :: l) = inputs_m l.
Proof using.
intros.
Admitted.

Lemma list_destruct_last : forall A (l : list A), l = [] \/ exists l' x, l = l' ++ [x].
Proof using.
induction l; intuition.
-
subst.
right.
exists nil.
simpl.
eauto.
-
break_exists.
subst.
right.
eexists.
eexists.
rewrite app_comm_cons.
Admitted.

Lemma inputs_1_app : forall tr1 tr2, inputs_1 (tr1 ++ tr2) = inputs_1 tr1 ++ inputs_1 tr2.
Proof using.
unfold inputs_1.
Admitted.

Lemma outputs_1_app : forall tr1 tr2, outputs_1 (tr1 ++ tr2) = outputs_1 tr1 ++ outputs_1 tr2.
Proof using.
unfold outputs_1.
Admitted.

Lemma processInputs_app : forall l1 l2 d, processInputs d (l1 ++ l2) = let (d', os) := processInputs d l1 in let (d'', os') := processInputs d' l2 in (d'', os ++ os').
Proof using.
induction l1; intros; simpl in *; repeat break_match.
-
auto.
-
find_inversion.
find_higher_order_rewrite.
repeat break_match.
repeat find_inversion.
repeat find_rewrite.
find_inversion.
Admitted.

Lemma correspond_preserved_snoc : forall sigma tr_1 tr_m st sigma' st' i l, correspond st sigma tr_1 tr_m -> handler i st = (l, st') -> state (sigma' Primary) = state (sigma Primary) -> queue (sigma' Primary) = queue (sigma Primary) ++ [i] -> correspond st' sigma' (tr_1 ++ [(i,l)]) (tr_m ++ [(Primary, inl (Request i))]).
Proof using.
unfold correspond.
intros.
rewrite outputs_m_app, outputs_1_app in *.
repeat break_match.
rewrite app_ass.
simpl.
repeat find_rewrite.
rewrite processInputs_app in *.
repeat break_match.
repeat tuple_inversion.
simpl in *.
break_match.
tuple_inversion.
break_and.
subst.
find_rewrite.
tuple_inversion.
rewrite <- app_ass.
find_rewrite.
Admitted.

Lemma inputs_m_backup_singleton : forall i, inputs_m [(Backup, inl i)] = [].
Proof using.
Admitted.

Lemma inputs_m_backup : forall i l, inputs_m ((Backup, inl i) :: l) = inputs_m l.
Proof using.
Admitted.

Lemma step_1_star_no_trace_no_step : forall st st' tr, step_1_star st st' tr -> tr = [] -> st = st'.
Proof using.
intros.
invc H; auto.
invc H1.
Admitted.

Lemma inputs_1_nil_is_nil : forall tr, inputs_1 tr = nil -> tr = nil.
Proof using.
intros.
destruct tr; auto.
Admitted.

Lemma correspond_preserved_primary_same_no_outputs : forall sigma sigma' st tr_1 tr_m tr_m', correspond st sigma tr_1 tr_m -> sigma' Primary = sigma Primary -> outputs_m tr_m' = [] -> correspond st sigma' tr_1 (tr_m ++ tr_m').
Proof using.
unfold correspond.
intros.
rewrite outputs_m_app.
repeat find_rewrite.
rewrite app_nil_r.
auto.
