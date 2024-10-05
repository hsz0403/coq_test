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

Lemma outputs_m_inl_singleton : forall h i, outputs_m [(h, inl i)] = [].
Proof using.
Admitted.

Lemma inputs_1_singleton : forall l i, inputs_1 l = [i] -> exists os, l = [(i, os)].
Proof using.
intros.
destruct l; simpl in *.
-
discriminate.
-
find_inversion.
find_apply_lem_hyp inputs_1_nil_is_nil.
subst.
destruct p.
Admitted.

Lemma step_1_star_singleton_trace : forall st st' i os, step_1_star st st' [(i, os)] -> step_1 st st' [(i, os)].
Proof using.
intros.
invc H.
invc H4.
-
rewrite app_nil_r in *.
subst.
auto.
-
invc H1.
invc H.
Admitted.

Lemma step_1_singleton_inversion : forall st st' i os, step_1 st st' [(i, os)] -> handler i st = (os, st').
Proof using.
intros.
invc H.
Admitted.

Lemma inputs_m_on_nil' : inputs_m (@nil (name * (PB_input + (list PB_output)))) = [].
Proof using.
unfold inputs_m.
Admitted.

Lemma correspond_init : correspond init PB_init [] [].
Proof using.
unfold correspond.
break_let.
simpl in *.
tuple_inversion.
Admitted.

Lemma inputs_1_invert_app : forall tr tr' x, inputs_1 tr = tr' ++ [x] -> exists y z, tr = y ++ [z] /\ inputs_1 y = tr' /\ inputs_1 [z] = [x].
Proof using.
intros tr.
pose proof list_destruct_last _ tr.
intuition.
-
subst.
destruct tr'; discriminate.
-
break_exists.
subst.
rewrite inputs_1_app in *.
simpl in *.
find_apply_lem_hyp app_inj_tail.
Admitted.

Lemma step_1_snoc_inv : forall st st' tr t, step_1_star st st' (tr ++ [t]) -> exists st2, step_1_star st st2 tr /\ step_1 st2 st' [t].
Proof using.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
invc H.
-
destruct tr; discriminate.
-
invc H4.
exists x'.
find_apply_lem_hyp app_inj_tail.
intuition.
subst.
+
apply refl_trans_n1_1n_trace.
auto.
+
subst.
constructor.
Admitted.

Lemma outputs_m_read_response_singleton : forall h o, outputs_m [(h, inr [ReadResponse o])] = [].
Proof using.
intros.
simpl in *.
Admitted.

Lemma correspond_reachable : forall net tr_m, step_async_star step_async_init net tr_m -> forall st tr_1, step_1_star init st tr_1 -> inputs_1 tr_1 = inputs_m tr_m -> correspond st (nwState net) tr_1 tr_m.
Proof using.
intros net tr_m H.
find_apply_lem_hyp refl_trans_1n_n1_trace.
prep_induction H.
induction H; intros; subst.
-
simpl in *.
rewrite inputs_m_on_nil' in H3.
destruct tr_1; try discriminate.
invc H.
+
simpl.
apply correspond_init.
+
invc H1.
discriminate.
-
repeat concludes.
invc H1; simpl in *.
+
find_apply_lem_hyp PB_net_defn.
intuition; subst; try rewrite inputs_m_app in *; try rewrite inputs_m_inr_singleton in *; try rewrite app_nil_r in *; try break_exists; try break_let; try break_and; subst; repeat find_rewrite; eauto using correspond_preserved_primary_same_no_outputs, correspond_preserved_primary_apply_entry, update_nop, update_eq, update_diff, outputs_m_inr_nil_singleton.
+
find_apply_lem_hyp PB_input_handler_defn.
intuition; subst; repeat rewrite snoc_assoc in *; repeat rewrite inputs_m_app in *.
*
break_exists.
break_and.
subst.
rewrite inputs_m_inr_singleton in *.
rewrite app_nil_r in *.
rewrite inputs_m_primary_inl_request_singleton in *.
find_apply_lem_hyp inputs_1_invert_app.
break_exists.
break_and.
subst.
simpl in *.
find_inversion.
destruct x1.
find_apply_lem_hyp step_1_snoc_inv.
break_exists.
break_and.
{
eapply correspond_preserved_primary_same_no_outputs; eauto.
eapply correspond_preserved_snoc; eauto.
-
eauto using step_1_singleton_inversion.
-
rewrite update_eq by auto.
auto.
-
rewrite update_eq by auto.
auto.
}
*
rewrite inputs_m_inr_singleton in *.
rewrite app_nil_r in *.
rewrite inputs_m_inl_read_singleton in *.
rewrite app_nil_r in *.
eauto using correspond_preserved_primary_same_no_outputs, update_nop, outputs_m_inl_read_singleton, outputs_m_read_response_singleton.
*
rewrite inputs_m_inr_singleton in *.
rewrite inputs_m_backup_singleton in *.
repeat rewrite app_nil_r in *.
Admitted.

Lemma step_async_outputs_m : forall net net' tr, step_async net net' tr -> (inputs_m tr = [] /\ (outputs_m tr = [] /\ nwState net Primary = nwState net' Primary)) \/ (inputs_m tr = [] /\ exists os, outputs_m tr = [os]) \/ (exists i, inputs_m tr = [i]).
Proof using.
intros.
invc H; simpl; break_match; auto; repeat rewrite app_nil_r in *; simpl in *; try find_apply_lem_hyp PB_net_defn; try find_apply_lem_hyp PB_input_handler_defn; intuition; subst.
-
rewrite inputs_m_inr_singleton.
rewrite update_eq by auto.
auto.
-
rewrite inputs_m_inr_singleton.
rewrite update_eq by auto.
auto.
-
break_exists.
intuition; break_match.
+
intuition.
subst.
rewrite inputs_m_inr_singleton.
simpl.
eauto.
+
break_exists.
intuition.
subst.
rewrite inputs_m_inr_singleton.
simpl.
eauto.
-
rewrite inputs_m_inr_singleton.
rewrite update_diff by auto.
auto.
-
rewrite inputs_m_inr_singleton.
rewrite update_diff by auto.
auto.
-
break_exists.
intuition; subst; rewrite inputs_m_primary_inl; eauto.
-
rewrite inputs_m_inl_read.
rewrite update_eq by auto.
auto.
-
rewrite inputs_m_inl_read.
rewrite update_diff by auto.
auto.
-
rewrite inputs_m_backup.
rewrite update_diff by auto.
Admitted.

Lemma network_invariant_inductive : forall net net' tr, step_async net net' tr -> network_invariant net -> network_invariant net'.
Proof using.
intros.
invc H; simpl in *.
-
unfold network_invariant in *.
simpl.
find_apply_lem_hyp PB_net_defn'.
workhorse; auto; intuition eauto.
-
unfold network_invariant in *.
simpl.
find_apply_lem_hyp PB_input_handler_defn.
Admitted.

Lemma network_invariant_init : network_invariant step_async_init.
Proof using.
unfold network_invariant.
simpl.
Admitted.

Lemma correspond_Prefix : forall st net tr_1 tr_m, correspond st (nwState net) tr_1 tr_m -> Prefix (outputs_m tr_m) (outputs_1 tr_1).
Proof using.
unfold correspond.
intros.
break_let.
intuition.
subst.
Admitted.

Lemma revert_state_defn : forall net, revert_state net = state (nwState net Primary).
Proof using.
unfold revert_state.
Admitted.

Lemma inductive_simulation : forall net net' tr, step_async net net' tr -> step_1_star (revert_state net) (revert_state net') (revert_trace tr).
Proof using.
intros.
invc H.
-
repeat rewrite revert_state_defn.
simpl.
rewrite app_nil_r.
simpl in *.
find_apply_lem_hyp PB_net_defn.
intuition; subst.
+
rewrite update_nop.
constructor.
+
rewrite update_nop.
constructor.
+
break_exists.
intuition; break_let.
*
intuition.
subst.
rewrite <- app_nil_r.
econstructor; constructor.
repeat find_rewrite.
rewrite update_eq by auto.
auto.
*
break_exists.
intuition.
subst.
simpl in *.
rewrite <- app_nil_r.
econstructor; constructor.
repeat find_rewrite.
rewrite update_eq by auto.
auto.
+
repeat find_rewrite.
rewrite update_diff by auto.
constructor.
-
repeat rewrite revert_state_defn.
simpl in *.
find_apply_lem_hyp PB_input_handler_defn.
intuition; subst.
+
rewrite update_eq by auto.
repeat find_rewrite.
constructor.
+
rewrite update_nop.
constructor.
+
rewrite update_diff by auto.
Admitted.

Lemma revert_trace_app : forall tr1 tr2, revert_trace (tr1 ++ tr2) = revert_trace tr1 ++ revert_trace tr2.
Proof using.
induction tr1; intros; simpl.
-
auto.
-
rewrite IHtr1.
repeat break_match; subst.
+
auto.
+
rewrite app_ass.
Admitted.

Lemma simulation : forall net tr, step_async_star step_async_init net tr -> step_1_star init (revert_state net) (revert_trace tr).
Proof using.
intros.
apply refl_trans_1n_n1_trace in H.
prep_induction H.
induction H; intros; subst.
-
unfold step_async_init, revert_state.
constructor.
-
repeat concludes.
rewrite revert_trace_app.
unfold step_1_star.
find_apply_lem_hyp inductive_simulation.
simpl in *.
unfold step_1_star in *.
Admitted.

Theorem transformer : forall (P : list (input * output) -> Prop), (forall st tr, step_1_star init st tr -> P tr) -> (forall net tr, step_async_star step_async_init net tr -> P (revert_trace tr)).
Proof using.
intros.
find_apply_lem_hyp simulation.
Admitted.

Lemma inputs_m_on_cons : forall t tr, inputs_m (t :: tr) = match t with | (Primary, inl (Request i)) => i :: inputs_m tr | _ => inputs_m tr end.
Proof using.
unfold inputs_m.
intros.
simpl.
Admitted.

Lemma correspond_inductive : forall net net' tr_m', step_async net net' tr_m' -> forall st st' tr_m tr_1 tr_1', correspond st (nwState net) tr_1 tr_m -> step_1_star st st' tr_1' -> inputs_1 tr_1' = inputs_m tr_m' -> correspond st' (nwState net') (tr_1 ++ tr_1') (tr_m ++ tr_m').
Proof using.
intros.
invc H; repeat break_let; simpl in *; repeat match goal with | [ H : context [ inputs_m [(_, inr _)] ] |- _ ] => rewrite inputs_m_inr_singleton in H | [ H : context [ inputs_m [(Primary, inl (Request _))] ] |- _ ] => rewrite inputs_m_primary_inl_request_singleton in H | [ H : context [ inputs_m ((Primary, inl (Request _)) :: _) ] |- _ ] => rewrite inputs_m_primary_inl in H | [ H : context [ inputs_m [(_, inl Read)] ] |- _ ] => rewrite inputs_m_inl_read_singleton in H | [ H : context [ inputs_m ((_, inl Read) :: _) ] |- _ ] => rewrite inputs_m_inl_read in H | [ H : context [ inputs_1 _ = [] ] |- _ ] => apply inputs_1_nil_is_nil in H; subst | [ H : context [ inputs_m [_] ] |- _ ] => rewrite inputs_m_backup_singleton in H | [ H : context [ inputs_m (_ :: _) ] |- _ ] => rewrite inputs_m_backup in H | [ H : step_1_star _ _ [] |- _ ] => apply step_1_star_no_trace_no_step in H; [|solve [auto]]; subst | [ H : step_1_star _ _ [_] |- _ ] => apply step_1_star_singleton_trace in H | [ H : step_1 _ _ [_] |- _ ] => apply step_1_singleton_inversion in H | [ |- context [ _ ++ [] ] ] => repeat rewrite app_nil_r | [ H : context [ _ ++ [] ] |- _ ] => repeat rewrite app_nil_r in * | [ H : context [ [] ++ _ ] |- _ ] => repeat rewrite app_nil_l in * | [ H : context [PB_net _ _ _ _] |- _ ] => apply PB_net_defn in H | [ H : context [PB_input_handler _ _ _] |- _ ] => apply PB_input_handler_defn in H | [ H : context [inputs_1 _ = [_]] |- _ ] => apply inputs_1_singleton in H | [ H : _ /\ _ |- _ ] => break_and | [ H : exists _, _ |- _ ] => break_exists | [ H : _ \/ _ |- _ ] => break_or_hyp | _ => repeat break_let; repeat find_rewrite; repeat tuple_inversion; subst; auto end; repeat rewrite snoc_assoc; eauto using correspond_preserved_primary_same_no_outputs, update_nop, update_diff, outputs_m_inr_nil_singleton, outputs_m_inl_read_singleton, outputs_m_read_response_singleton.
-
eapply correspond_preserved_primary_apply_entry; eauto using update_eq.
-
eapply correspond_preserved_primary_apply_entry; eauto using update_eq.
-
eapply correspond_preserved_primary_same_no_outputs; eauto.
eapply correspond_preserved_snoc; eauto; rewrite update_eq by auto; repeat find_rewrite; auto.
-
eapply correspond_preserved_primary_same_no_outputs; eauto.
eapply correspond_preserved_snoc; eauto; rewrite update_eq by auto; repeat find_rewrite; auto.
