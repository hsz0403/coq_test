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

Definition op_eq_dec : forall x y : op, {x = y} + {x <> y}.
Proof using K_eq_dec.
Admitted.

Definition IR_eq_dec : forall x y : IR, {x = y} + {x <> y}.
Proof using K_eq_dec.
Admitted.

Lemma acknowledge_all_ops_was_in : forall l ir, acknowledge_all_ops l ir -> forall k, In (IRI k) ir -> In (I k) l.
Proof using.
Admitted.

Lemma acknowledge_all_ops_func_defn : forall x l target, acknowledge_all_ops_func (x :: l) target = match x with | I k => if acknowledged_op_dec k l then IRI k :: acknowledge_all_ops_func l target else if in_dec IR_eq_dec (IRU k) target then IRI k :: IRU k :: acknowledge_all_ops_func l target else acknowledge_all_ops_func l target | O k => IRO k :: acknowledge_all_ops_func l target end.
Proof using.
intros.
unfold acknowledge_all_ops_func.
Admitted.

Lemma acknowledge_all_ops_func_correct : forall l target, acknowledge_all_ops l (acknowledge_all_ops_func l target).
Proof using.
Admitted.

Lemma acknowledge_all_ops_func_target_ext : forall l t t', (forall k, In (IRU k) t -> In (IRU k) t') -> (forall k, In (IRU k) t' -> In (IRU k) t) -> acknowledge_all_ops_func l t = acknowledge_all_ops_func l t'.
Proof using.
induction l; simpl in *; repeat break_match; subst; intuition eauto using f_equal.
Admitted.

Lemma IR_equivalent_refl : forall l, IR_equivalent l l.
Proof using.
Admitted.

Lemma IR_equiv_in_l_r : forall ir1 ir2, IR_equivalent ir1 ir2 -> forall o, In o ir1 -> In o ir2.
Proof using.
Admitted.

Lemma IR_equiv_in_r_l : forall ir1 ir2, IR_equivalent ir1 ir2 -> forall o, In o ir2 -> In o ir1.
Proof using.
Admitted.

Lemma IR_equiv_Permutation : forall ir1 ir2, IR_equivalent ir1 ir2 -> Permutation ir1 ir2.
Proof using.
Admitted.

Lemma IR_equiv_app_head : forall l xs ys, IR_equivalent xs ys -> IR_equivalent (l ++ xs) (l ++ ys).
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
Admitted.

Lemma op_equiv_Permutation : forall xs ys, op_equivalent xs ys -> Permutation xs ys.
Proof using.
Admitted.

Lemma op_equiv_ack_op_lr : forall xs ys, op_equivalent xs ys -> forall k, acknowledged_op k xs -> acknowledged_op k ys.
Proof using.
unfold acknowledged_op.
intros.
Admitted.

Lemma IR_equiv_snoc : forall xs ys x, IR_equivalent xs ys -> IR_equivalent (xs ++ [x]) (ys ++ [x]).
Proof using.
induction 1; simpl; eauto.
