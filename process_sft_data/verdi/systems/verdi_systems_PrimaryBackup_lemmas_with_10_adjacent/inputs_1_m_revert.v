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

Lemma ZOOOPST_nil : forall A B C, @zero_or_one_outputs_per_step_trace A B C [].
Proof using.
unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
simpl.
Admitted.

Lemma ZOOOPST_head : forall A B C x y, @zero_or_one_outputs_per_step_trace A B C (x :: y) -> zero_or_one_outputs_per_step x.
Proof using.
unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
simpl.
Admitted.

Lemma ZOOOPST_tail : forall A B C x y, @zero_or_one_outputs_per_step_trace A B C (x :: y) -> zero_or_one_outputs_per_step_trace y.
Proof using.
unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
simpl.
Admitted.

Lemma ZOOOPST_cons_elim : forall A B C x y, @zero_or_one_outputs_per_step_trace A B C (x :: y) -> zero_or_one_outputs_per_step x /\ zero_or_one_outputs_per_step_trace y.
Proof using.
Admitted.

Lemma ZOOOPST_cons_intro : forall A B C x y, @zero_or_one_outputs_per_step A B C x -> zero_or_one_outputs_per_step_trace y -> zero_or_one_outputs_per_step_trace (x :: y).
Proof using.
unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
simpl.
Admitted.

Lemma ZOOOPST_app : forall A B C xs ys, @zero_or_one_outputs_per_step_trace A B C xs -> zero_or_one_outputs_per_step_trace ys -> zero_or_one_outputs_per_step_trace (xs ++ ys).
Proof using.
induction xs; intros.
-
auto.
-
Admitted.

Lemma ZOOOPST_singleton_nil : forall A B C h, @zero_or_one_outputs_per_step_trace A B C [(h, inr [])].
Proof using.
unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
simpl in *.
intuition.
subst.
simpl in *.
find_inversion.
Admitted.

Lemma ZOOOPST_singleton_singleton : forall A B C h x, @zero_or_one_outputs_per_step_trace A B C [(h, inr [x])].
Proof using.
unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
simpl.
intuition.
subst.
simpl in *.
find_inversion.
Admitted.

Lemma ZOOOPST_singleton_inl : forall A B C h i, @zero_or_one_outputs_per_step_trace A B C [(h, inl i)].
Proof using.
unfold zero_or_one_outputs_per_step_trace, zero_or_one_outputs_per_step.
simpl.
intuition.
subst.
Admitted.

Theorem pbj_0_or_1 : forall net tr, step_async_star (params:=PB_multi_params) step_async_init net tr -> zero_or_one_outputs_per_step_trace tr.
Proof using.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
prep_induction H.
induction H; intros; subst.
-
auto using ZOOOPST_nil.
-
repeat concludes.
apply ZOOOPST_app; auto.
invc H1; simpl in *.
+
find_apply_lem_hyp PB_net_defn.
intuition; subst; auto using ZOOOPST_singleton_nil.
break_exists.
break_and.
break_match.
intuition; subst; auto using ZOOOPST_singleton_singleton.
+
rewrite cons_cons_app.
apply ZOOOPST_app.
*
auto using ZOOOPST_singleton_inl.
*
Admitted.

Lemma inputs_1_m_revert : forall net tr, step_async_star (params := PB_multi_params) step_async_init net tr -> inputs_m tr = inputs_1 (revert_trace tr) ++ queue (nwState net Primary).
Proof using.
intros.
find_apply_lem_hyp refl_trans_1n_n1_trace.
prep_induction H.
induction H; intros; subst.
-
simpl.
auto.
-
repeat concludes.
rewrite inputs_m_app.
rewrite revert_trace_app.
rewrite inputs_1_app.
rewrite IHrefl_trans_n1_trace.
repeat rewrite app_ass.
f_equal.
invc H1; simpl in *.
+
find_apply_lem_hyp PB_net_defn.
intuition; subst; simpl in *; rewrite (inputs_m_inr_singleton); rewrite app_nil_r.
*
rewrite update_nop.
auto.
*
repeat find_rewrite.
rewrite update_nop.
auto.
*
break_exists.
break_let.
{
intuition; subst.
-
repeat find_rewrite.
rewrite app_nil_r.
simpl.
rewrite update_eq by auto.
auto.
-
break_exists.
intuition.
subst.
repeat find_rewrite.
simpl.
rewrite update_eq by auto.
auto.
}
*
break_exists.
intuition.
repeat find_rewrite.
rewrite update_diff by auto.
auto.
+
find_apply_lem_hyp PB_input_handler_defn.
intuition; subst; simpl in *.
*
break_exists.
intuition; subst; rewrite (inputs_m_primary_inl); rewrite update_eq; auto.
*
rewrite (inputs_m_inl_read).
rewrite inputs_m_inr_singleton.
rewrite app_nil_r.
rewrite update_nop.
auto.
*
rewrite (inputs_m_backup).
rewrite inputs_m_inr_singleton.
rewrite app_nil_r.
rewrite update_nop.
auto.
