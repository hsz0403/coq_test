Require Import Verdi.Verdi.
Section Linearizability.
Variable K : Type.
Variable K_eq_dec : forall x y : K, {x = y} + {x <> y}.
Inductive op : Type := | I : K -> op | O : K -> op.
Definition op_eq_dec : forall x y : op, {x = y} + {x <> y}.
Proof using K_eq_dec.
decide equality.
Inductive IR : Type := | IRI : K -> IR | IRO : K -> IR | IRU : K -> IR.
Definition IR_eq_dec : forall x y : IR, {x = y} + {x <> y}.
Proof using K_eq_dec.
decide equality.
Definition acknowledged_op (k : K) (trace : list op) := In (O k) trace.
Definition acknowledged_op_dec (k : K) (tr : list op) : {acknowledged_op k tr} + {~acknowledged_op k tr} := in_dec op_eq_dec (O k) tr.
Inductive acknowledge_all_ops : list op -> list IR -> Prop := | AAO_nil : acknowledge_all_ops [] [] | AAO_IU : forall k tr out, ~ acknowledged_op k tr -> acknowledge_all_ops tr out -> acknowledge_all_ops (I k :: tr) (IRI k :: IRU k :: out) | AAO_I_dorp : forall k tr out, ~ acknowledged_op k tr -> acknowledge_all_ops tr out -> acknowledge_all_ops (I k :: tr) out | AAO_IO : forall k tr out, acknowledged_op k tr -> acknowledge_all_ops tr out -> acknowledge_all_ops (I k :: tr) (IRI k :: out) | AAO_O : forall k tr out, acknowledge_all_ops tr out -> acknowledge_all_ops (O k :: tr) (IRO k :: out).
Fixpoint acknowledge_all_ops_func (l : list op) (target : list IR) : list IR := match l with | [] => [] | x :: xs => match x with | I k => if acknowledged_op_dec k xs then IRI k :: acknowledge_all_ops_func xs target else if in_dec IR_eq_dec (IRU k) target then IRI k :: IRU k :: acknowledge_all_ops_func xs target else acknowledge_all_ops_func xs target | O k => IRO k :: acknowledge_all_ops_func xs target end end.
Hint Constructors acknowledge_all_ops : core.
Definition good_move (x y : IR) : Prop := (forall k k', ~ (x = IRO k /\ y = IRI k')) /\ (forall k, ~ (x = IRI k /\ y = IRO k)) /\ (forall k, ~ (x = IRI k /\ y = IRU k)).
Inductive IR_equivalent : list IR -> list IR -> Prop := | IR_equiv_nil : IR_equivalent [] [] | IR_equiv_cons : forall x xs ys, IR_equivalent xs ys -> IR_equivalent (x :: xs) (x :: ys) | IR_equiv_move : forall x y xs ys, IR_equivalent xs ys -> good_move x y -> IR_equivalent (x :: y :: xs) (y :: x :: ys) | IR_equiv_trans : forall l1 l2 l3, IR_equivalent l1 l2 -> IR_equivalent l2 l3 -> IR_equivalent l1 l3.
Hint Constructors IR_equivalent : core.
Hint Constructors Permutation : core.
Section Examples.
Example IR_equiv_eg1 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k; IRO k'] [IRI k; IRO k; IRI k'; IRO k'].
Proof using.
intros.
constructor.
econstructor; auto.
red.
intuition (auto; congruence).
Example IR_equiv_eg2 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k; IRO k'] [IRI k'; IRO k'; IRI k; IRO k].
Proof using.
intros.
eapply IR_equiv_trans with (l2 := [IRI k; IRI k'; IRO k'; IRO k]).
-
repeat constructor; unfold good_move; intuition (try congruence).
-
eapply IR_equiv_trans with (l2 := [IRI k'; IRI k; IRO k'; IRO k]).
+
apply IR_equiv_move; auto using IR_equivalent_refl.
red.
intuition congruence.
+
constructor.
apply IR_equiv_move; auto.
red.
intuition congruence.
Example IR_equiv_eg3 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k'; IRO k] [IRI k'; IRO k'; IRI k; IRO k].
Proof using.
intros.
eapply IR_equiv_trans with (l2 := [IRI k'; IRI k; IRO k'; IRO k]).
-
constructor.
+
apply IR_equivalent_refl.
+
red.
intuition congruence.
-
constructor.
constructor.
+
apply IR_equivalent_refl.
+
red.
intuition congruence.
Example IR_equiv_eg4 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k'; IRO k] [IRI k; IRO k; IRI k'; IRO k'].
Proof using.
intros.
constructor.
eapply IR_equiv_trans with (l2 := [IRI k'; IRO k; IRO k']).
-
repeat constructor; unfold good_move; intuition congruence.
-
eapply IR_equiv_move; auto.
red.
intuition congruence.
End Examples.
Fixpoint good_trace (l : list IR) : Prop := match l with | [] => True | IRI k :: IRO k' :: l' => k = k' /\ good_trace l' | IRI k :: IRU k' :: l' => k = k' /\ good_trace l' | _ => False end.
Definition equivalent (l : list op) (ir : list IR) : Prop := good_trace ir /\ exists ir', acknowledge_all_ops l ir' /\ IR_equivalent ir' ir.
Definition get_op_input_keys (l : list op) : list K := filterMap (fun x => match x with | I k => Some k | _ => None end) l.
Definition get_IR_input_keys (l : list IR) : list K := filterMap (fun x => match x with | IRI k => Some k | _ => None end) l.
Definition get_op_output_keys (l : list op) : list K := filterMap (fun x => match x with | O k => Some k | _ => None end) l.
Definition get_IR_output_keys (l : list IR) : list K := filterMap (fun x => match x with | IRO k => Some k | IRU k => Some k | _ => None end) l.
Fixpoint good_trace_ind' (P : list IR -> Prop -> Prop) (l : list IR) : P [] True -> (forall k, P [IRI k] False) -> (forall k k' l, P (IRI k :: IRI k' :: l) False) -> (forall k k' l, P l (good_trace l) -> P (IRI k :: IRO k' :: l) (k = k' /\ good_trace l)) -> (forall k k' l, P l (good_trace l) -> P (IRI k :: IRU k' :: l) (k = k' /\ good_trace l)) -> (forall k l, P (IRO k :: l) False) -> (forall k l, P (IRU k :: l) False) -> P l (good_trace l).
Proof using.
intros.
destruct l; simpl; repeat break_match; auto; subst.
-
match goal with | [ H : context [IRI _ :: IRO _ :: _ ] |- _ ] => apply H end.
apply good_trace_ind'; auto.
-
match goal with | [ H : context [IRI _ :: IRU _ :: _ ] |- _ ] => apply H end.
apply good_trace_ind'; auto.
Definition good_op_move (x y : op) : Prop := (forall k k', ~ (x = O k /\ y = I k')) /\ (forall k, ~ (x = I k /\ y = O k)).
Inductive op_equivalent : list op -> list op -> Prop := | op_equiv_nil : op_equivalent [] [] | op_equiv_cons : forall x xs ys, op_equivalent xs ys -> op_equivalent (x :: xs) (x :: ys) | op_equiv_move : forall x y xs ys, good_op_move x y -> op_equivalent xs ys -> op_equivalent (x :: y :: xs) (y :: x :: ys) | op_equiv_trans : forall l1 l2 l3, op_equivalent l1 l2 -> op_equivalent l2 l3 -> op_equivalent l1 l3.
Hint Resolve IR_equivalent_refl : core.
Hint Resolve good_move_II : core.
Hint Resolve good_move_U_l : core.
Hint Constructors op_equivalent : core.
Ltac start := match goal with | [ H : good_trace (_ :: _) |- _ ] => simpl in H end; break_and; subst; match goal with | [ H : context [In (?c _) (_ :: ?c ?k' :: _) -> In _ ?l] |- _ ] => assert (In (O k') l) by firstorder; assert (before (I k') (O k') l) by auto; repeat rewrite get_IR_input_keys_defn in *; repeat rewrite get_IR_output_keys_defn in *; repeat match goal with | [ H : NoDup (_ :: _) |- _ ] => invc H end; assert (In (I k') l) by eauto using before_In; assert (forall x, before x (I k') l -> exists k, x = I k) by eauto using before_head_op; find_copy_apply_lem_hyp before_split; auto; try congruence; break_exists; subst end; repeat match goal with | [ H : In ?x (_ ++ ?x :: _) |- _ ] => clear H | [ H : In ?x (_ ++ _ :: _ ++ ?x :: _) |- _ ] => clear H end.
End Linearizability.
Arguments I {_} _.
Arguments O {_} _.
Arguments IRI {_} _.
Arguments IRO {_} _.
Arguments IRU {_} _.

Lemma IR_equiv_Permutation : forall ir1 ir2, IR_equivalent ir1 ir2 -> Permutation ir1 ir2.
Proof using.
Admitted.

Lemma IR_equiv_app_head : forall l xs ys, IR_equivalent xs ys -> IR_equivalent (l ++ xs) (l ++ ys).
Proof using.
Admitted.

Lemma IR_equiv_snoc : forall xs ys x, IR_equivalent xs ys -> IR_equivalent (xs ++ [x]) (ys ++ [x]).
Proof using.
Admitted.

Lemma IR_equiv_app_tail : forall l xs ys, IR_equivalent xs ys -> IR_equivalent (xs ++ l) (ys ++ l).
Proof using.
Admitted.

Example IR_equiv_eg1 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k; IRO k'] [IRI k; IRO k; IRI k'; IRO k'].
Proof using.
intros.
constructor.
econstructor; auto.
red.
Admitted.

Example IR_equiv_eg2 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k; IRO k'] [IRI k'; IRO k'; IRI k; IRO k].
Proof using.
intros.
eapply IR_equiv_trans with (l2 := [IRI k; IRI k'; IRO k'; IRO k]).
-
repeat constructor; unfold good_move; intuition (try congruence).
-
eapply IR_equiv_trans with (l2 := [IRI k'; IRI k; IRO k'; IRO k]).
+
apply IR_equiv_move; auto using IR_equivalent_refl.
red.
intuition congruence.
+
constructor.
apply IR_equiv_move; auto.
red.
Admitted.

Example IR_equiv_eg3 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k'; IRO k] [IRI k'; IRO k'; IRI k; IRO k].
Proof using.
intros.
eapply IR_equiv_trans with (l2 := [IRI k'; IRI k; IRO k'; IRO k]).
-
constructor.
+
apply IR_equivalent_refl.
+
red.
intuition congruence.
-
constructor.
constructor.
+
apply IR_equivalent_refl.
+
red.
Admitted.

Example IR_equiv_eg4 : forall k k', k <> k' -> IR_equivalent [IRI k; IRI k'; IRO k'; IRO k] [IRI k; IRO k; IRI k'; IRO k'].
Proof using.
intros.
constructor.
eapply IR_equiv_trans with (l2 := [IRI k'; IRO k; IRO k']).
-
repeat constructor; unfold good_move; intuition congruence.
-
eapply IR_equiv_move; auto.
red.
Admitted.

Lemma acknowledge_all_ops_func_IRU_In : forall l ir k, In (IRU k) (acknowledge_all_ops_func l ir) -> In (I k) l.
Proof using.
Admitted.

Lemma get_op_input_keys_defn : forall x l, get_op_input_keys (x :: l) = match x with | I k => k :: get_op_input_keys l | _ => get_op_input_keys l end.
Proof using.
unfold get_op_input_keys.
intros.
simpl.
Admitted.

Lemma get_IR_input_keys_defn : forall x l, get_IR_input_keys (x :: l) = match x with | IRI k => k :: get_IR_input_keys l | _ => get_IR_input_keys l end.
Proof using.
unfold get_IR_input_keys.
intros.
simpl.
Admitted.

Lemma get_op_output_keys_defn : forall x l, get_op_output_keys (x :: l) = match x with | O k => k :: get_op_output_keys l | _ => get_op_output_keys l end.
Proof using.
unfold get_op_output_keys.
intros.
simpl.
Admitted.

Lemma get_IR_output_keys_defn : forall x l, get_IR_output_keys (x :: l) = match x with | IRO k => k :: get_IR_output_keys l | IRU k => k :: get_IR_output_keys l | _ => get_IR_output_keys l end.
Proof using.
unfold get_IR_output_keys.
intros.
simpl.
Admitted.

Fixpoint good_trace_ind' (P : list IR -> Prop -> Prop) (l : list IR) : P [] True -> (forall k, P [IRI k] False) -> (forall k k' l, P (IRI k :: IRI k' :: l) False) -> (forall k k' l, P l (good_trace l) -> P (IRI k :: IRO k' :: l) (k = k' /\ good_trace l)) -> (forall k k' l, P l (good_trace l) -> P (IRI k :: IRU k' :: l) (k = k' /\ good_trace l)) -> (forall k l, P (IRO k :: l) False) -> (forall k l, P (IRU k :: l) False) -> P l (good_trace l).
Proof using.
intros.
destruct l; simpl; repeat break_match; auto; subst.
-
match goal with | [ H : context [IRI _ :: IRO _ :: _ ] |- _ ] => apply H end.
apply good_trace_ind'; auto.
-
match goal with | [ H : context [IRI _ :: IRU _ :: _ ] |- _ ] => apply H end.
Admitted.

Lemma good_trace_ind : forall P : list IR -> Prop -> Prop, P [] True -> (forall k, P [IRI k] False) -> (forall k k' ir, P (IRI k :: IRI k' :: ir) False) -> (forall k k' ir, P ir (good_trace ir) -> P (IRI k :: IRO k' :: ir) (k = k' /\ good_trace ir)) -> (forall k k' ir, P ir (good_trace ir) -> P (IRI k :: IRU k' :: ir) (k = k' /\ good_trace ir)) -> (forall k ir, P (IRO k :: ir) False) -> (forall k ir, P (IRU k :: ir) False) -> forall ir, P ir (good_trace ir).
Proof using.
intros.
Admitted.

Lemma good_trace_IRI_in : forall ir, good_trace ir -> forall k, In (IRI k) ir -> In (IRO k) ir \/ In (IRU k) ir.
Proof using.
intros ir.
induction ir, good_trace using good_trace_ind; intros; simpl in *; intuition (auto; try congruence).
-
subst.
find_apply_hyp_hyp.
intuition.
-
subst.
find_apply_hyp_hyp.
Admitted.

Lemma acknowledge_all_ops_func_target_nil : forall l, (forall k, ~ In (O k) l) -> acknowledge_all_ops_func l [] = [].
Proof using.
induction l; intros; simpl in *.
-
auto.
-
Admitted.

Lemma before_head_op : forall l h ir, (forall k1 k2, In (I k2) l -> before (O k1) (I k2) l -> before (IRO k1) (IRI k2) (IRI h :: ir)) -> forall x, In (I h) l -> before x (I h) l -> exists k, x = I k.
Proof using.
intros.
destruct x.
eauto.
eapply_prop_hyp In In; eauto.
simpl in *.
Admitted.

Lemma good_move_II : forall k k', good_move (IRI k) (IRI k').
Proof using.
red.
Admitted.

Lemma good_move_OO : forall k k', good_move (IRO k) (IRO k').
Proof using.
red.
Admitted.

Lemma op_equiv_Permutation : forall xs ys, op_equivalent xs ys -> Permutation xs ys.
Proof using.
Admitted.

Lemma op_equiv_ack_op_lr : forall xs ys, op_equivalent xs ys -> forall k, acknowledged_op k xs -> acknowledged_op k ys.
Proof using.
unfold acknowledged_op.
intros.
Admitted.

Lemma op_equiv_ack_op_rl : forall xs ys, op_equivalent xs ys -> forall k, acknowledged_op k ys -> acknowledged_op k xs.
Proof using.
unfold acknowledged_op.
intros.
Admitted.

Lemma acknowledged_op_defn : forall k xs, acknowledged_op k xs -> In (O k) xs.
Proof using.
Admitted.

Lemma good_move_U_l : forall k x, good_move (IRU k) x.
Proof using.
red.
Admitted.

Lemma good_move_IU_neq : forall k k', k <> k' -> good_move (IRI k) (IRU k').
Proof using.
red.
Admitted.

Lemma good_move_IO_neq : forall k k', k <> k' -> good_move (IRI k) (IRO k').
Proof using.
red.
Admitted.

Lemma not_good_op_move_IO : forall k, good_op_move (I k) (O k) -> False.
Proof using.
unfold good_op_move.
Admitted.

Lemma not_good_op_move_OI : forall k k', good_op_move (O k) (I k') -> False.
Proof using.
unfold good_op_move.
Admitted.

Lemma good_op_move_good_move_IO : forall k k', good_op_move (I k) (O k') -> good_move (IRI k) (IRO k').
Proof using.
unfold good_op_move, good_move.
intuition (try congruence).
repeat find_inversion.
Admitted.

Lemma good_op_move_cases : forall x y, good_op_move x y -> exists k k', (x = I k /\ y = I k') \/ (x = O k /\ y = O k') \/ (k <> k' /\ x = I k /\ y = O k').
Proof using.
unfold good_op_move.
intros.
destruct x as [k|k], y as [k'|k']; exists k, k'; intuition.
-
right.
right.
intuition.
subst.
eauto.
-
exfalso.
Admitted.

Lemma acknowledged_op_I_cons_reduce : forall k k' l, acknowledged_op k (I k' :: l) -> acknowledged_op k l.
Proof using.
unfold acknowledged_op.
simpl.
Admitted.

Lemma acknowledged_op_I_cons_expand : forall k k' l, acknowledged_op k l -> acknowledged_op k (I k' :: l).
Proof using.
unfold acknowledged_op.
simpl.
Admitted.

Lemma IR_equiv_AAOF_I : forall k xs ys target, op_equivalent xs ys -> IR_equivalent (acknowledge_all_ops_func xs target) (acknowledge_all_ops_func ys target) -> IR_equivalent (acknowledge_all_ops_func (I k :: xs) target) (acknowledge_all_ops_func (I k :: ys) target).
Proof using.
intros.
simpl.
Admitted.

Lemma IR_equiv_AAOF_II_neq : forall xs ys target k k', k <> k' -> op_equivalent xs ys -> IR_equivalent (acknowledge_all_ops_func xs target) (acknowledge_all_ops_func ys target) -> IR_equivalent (acknowledge_all_ops_func (I k :: I k' :: xs) target) (acknowledge_all_ops_func (I k' :: I k :: ys) target).
Proof using.
intros.
rewrite acknowledge_all_ops_func_defn.
break_if.
-
rewrite acknowledge_all_ops_func_defn.
break_if; rewrite acknowledge_all_ops_func_defn with (l := _ :: _).
+
rewrite if_decider_true by eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr, acknowledged_op_I_cons_reduce.
rewrite acknowledge_all_ops_func_defn.
rewrite if_decider_true by eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr, acknowledged_op_I_cons_reduce.
auto.
+
rewrite if_decider_false with (dec := acknowledged_op_dec _) by intuition eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl, acknowledged_op_I_cons_reduce.
rewrite acknowledge_all_ops_func_defn.
rewrite if_decider_true with (dec := acknowledged_op_dec _) by eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr, acknowledged_op_I_cons_reduce.
break_if.
*
eauto 6 using good_move_IU_neq.
*
auto.
-
break_if; rewrite acknowledge_all_ops_func_defn.
+
break_if; rewrite acknowledge_all_ops_func_defn.
*
rewrite if_decider_true by eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr, acknowledged_op_I_cons_reduce.
rewrite acknowledge_all_ops_func_defn.
rewrite if_decider_false by intuition eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl, acknowledged_op_I_cons_reduce.
rewrite if_decider_true by auto.
eauto.
*
rewrite if_decider_false with (dec := acknowledged_op_dec _) by eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl, acknowledged_op_I_cons_reduce.
rewrite acknowledge_all_ops_func_defn.
rewrite if_decider_false with (dec := acknowledged_op_dec _) by eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl, acknowledged_op_I_cons_reduce.
rewrite if_decider_true with (dec := in_dec _ (IRU k)) by auto.
{
break_if.
-
eapply IR_equiv_trans; [apply IR_equiv_cons; apply IR_equiv_move; auto|].
eapply IR_equiv_trans; [apply IR_equiv_move; auto|].
constructor.
eapply IR_equiv_trans; [apply IR_equiv_cons; apply IR_equiv_move; auto|].
auto using good_move_IU_neq.
-
auto.
}
+
break_if; rewrite acknowledge_all_ops_func_defn.
*
rewrite if_decider_true with (dec := acknowledged_op_dec _) by eauto 3 using acknowledged_op_I_cons_expand, op_equiv_ack_op_lr, acknowledged_op_I_cons_reduce.
rewrite acknowledge_all_ops_func_defn.
rewrite if_decider_false with (dec := acknowledged_op_dec _) by eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl, acknowledged_op_I_cons_reduce.
rewrite if_decider_false by auto.
auto.
*
rewrite if_decider_false with (dec := acknowledged_op_dec _) by eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl, acknowledged_op_I_cons_reduce.
rewrite acknowledge_all_ops_func_defn.
rewrite if_decider_false with (dec := acknowledged_op_dec _) by eauto using acknowledged_op_I_cons_expand, op_equiv_ack_op_rl, acknowledged_op_I_cons_reduce.
rewrite if_decider_false with (dec := in_dec _ (IRU k)) by auto.
Admitted.

Lemma op_equiv_AAOF_IR_equiv : forall xs ys, op_equivalent xs ys -> forall l, IR_equivalent (acknowledge_all_ops_func xs l) (acknowledge_all_ops_func ys l).
Proof using.
induction 1; intros.
-
auto.
-
simpl.
repeat break_match; subst; auto; exfalso; eauto using op_equiv_ack_op_lr, op_equiv_ack_op_rl.
-
find_copy_apply_lem_hyp good_op_move_cases.
break_exists.
intuition; subst.
+
destruct (K_eq_dec x0 x1).
*
subst.
auto using IR_equiv_AAOF_I.
*
auto using IR_equiv_AAOF_II_neq.
+
simpl.
eauto using good_move_OO.
+
simpl.
repeat break_match; intuition; try congruence.
*
eauto using good_move_IO_neq.
*
exfalso.
eauto using op_equiv_ack_op_lr.
*
exfalso.
eauto using op_equiv_ack_op_lr.
*
exfalso; eauto using Permutation_in, op_equiv_Permutation, acknowledged_op_defn, Permutation_sym.
*
eapply IR_equiv_trans; [apply IR_equiv_cons; apply IR_equiv_move; auto|].
eapply IR_equiv_trans; [apply IR_equiv_move; auto|].
apply good_move_IO_neq.
congruence.
auto.
*
exfalso.
match goal with | [ H : In (O _) _ -> False |- _ ] => apply H end.
eapply Permutation_in; [apply Permutation_sym; eapply op_equiv_Permutation; eauto|].
auto using acknowledged_op_defn.
-
Admitted.

Lemma op_equivalent_refl : forall xs, op_equivalent xs xs.
Proof using.
Admitted.

Lemma good_op_move_II : forall k k', good_op_move (I k) (I k').
Proof using.
red.
Admitted.

Lemma op_equivalent_all_Is_I : forall l k, (forall x, In x l -> exists k, x = I k) -> op_equivalent (l ++ [I k]) (I k :: l).
Proof using.
induction l; intros; simpl in *; intuition.
apply op_equiv_trans with (l2 := (a :: I k :: l)).
-
auto.
-
specialize (H a).
concludes.
break_exists.
subst.
Admitted.

Lemma good_op_move_neq_IO : forall k k', k <> k' -> good_op_move (I k) (O k').
Proof using.
unfold good_op_move.
Admitted.

Lemma IR_equivalent_all_Is_I : forall l k, (forall x, In x l -> exists k, x = IRI k) -> IR_equivalent (l ++ [IRI k]) (IRI k :: l).
Proof using.
induction l; intros; simpl in *; intuition.
apply IR_equiv_trans with (l2 := (a :: IRI k :: l)).
-
auto.
-
specialize (H a).
concludes.
break_exists.
subst.
auto using IR_equivalent_refl, good_move_II.
