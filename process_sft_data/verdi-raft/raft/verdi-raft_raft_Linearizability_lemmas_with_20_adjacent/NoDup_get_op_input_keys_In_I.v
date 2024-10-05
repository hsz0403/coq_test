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

Lemma get_op_input_keys_sound : forall k l, In k (get_op_input_keys l) -> In (I k) l.
Proof using.
induction l; intros.
-
auto.
-
simpl in *.
rewrite get_op_input_keys_defn in *.
break_match; simpl in *.
+
subst.
intuition congruence.
+
Admitted.

Lemma get_op_output_keys_sound : forall k l, In k (get_op_output_keys l) -> In (O k) l.
Proof using.
induction l; intros.
-
auto.
-
simpl in *.
rewrite get_op_output_keys_defn in *.
break_match; simpl in *.
+
subst.
auto.
+
Admitted.

Lemma get_op_input_keys_on_Os_nil : forall l, (forall o, In o l -> exists k, o = O k) -> get_op_input_keys l = [].
Proof using.
induction l; intros; simpl in *; intuition.
rewrite get_op_input_keys_defn.
pose proof H a.
concludes.
break_exists.
subst.
Admitted.

Lemma get_op_input_keys_preserves_NoDup : forall l, NoDup l -> NoDup (get_op_input_keys l).
Proof using.
intros.
unfold get_op_input_keys.
apply filterMap_NoDup_inj; auto.
intros.
repeat break_match; try discriminate.
subst.
Admitted.

Lemma get_op_output_keys_preserves_NoDup : forall l, NoDup l -> NoDup (get_op_output_keys l).
Proof using.
intros.
unfold get_op_output_keys.
apply filterMap_NoDup_inj; auto.
intros.
repeat break_match; try discriminate.
subst.
Admitted.

Lemma get_op_output_keys_complete : forall xs k, In (O k) xs -> In k (get_op_output_keys xs).
Proof using.
unfold get_op_input_keys.
intros.
eapply filterMap_In; eauto.
Admitted.

Lemma get_IR_output_keys_complete_U : forall xs k, In (IRU k) xs -> In k (get_IR_output_keys xs).
Proof using.
unfold get_IR_output_keys.
intros.
eapply filterMap_In; eauto.
Admitted.

Lemma get_IR_output_keys_complete_O : forall xs k, In (IRO k) xs -> In k (get_IR_output_keys xs).
Proof using.
unfold get_IR_output_keys.
intros.
eapply filterMap_In; eauto.
Admitted.

Lemma get_IR_input_keys_complete : forall xs k, In (IRI k) xs -> In k (get_IR_input_keys xs).
Proof using.
unfold get_IR_input_keys.
intros.
eapply filterMap_In; eauto.
Admitted.

Lemma op_equivalent_all_Is_O_middle : forall xs ys k, (forall k', In (I k') xs -> k <> k') -> op_equivalent (xs ++ O k :: ys) (O k :: xs ++ ys).
Proof using.
intros.
rewrite app_comm_cons.
replace (xs ++ O k :: ys) with ((xs ++ [O k]) ++ ys) by now rewrite app_ass.
Admitted.

Lemma NoDup_get_op_output_keys_In_O : forall xs ys k, NoDup (get_op_output_keys (xs ++ O k :: ys)) -> In (O k) (xs ++ ys) -> False.
Proof using.
intros.
rewrite get_op_output_keys_app in *.
rewrite get_op_output_keys_defn in *.
do_in_app.
Admitted.

Lemma NoDup_get_op_output_keys_In_2_3 : forall xs ys zs k, NoDup (get_op_output_keys (xs ++ I k :: ys ++ O k :: zs)) -> In (O k) (xs ++ ys ++ zs) -> False.
Proof using.
intros.
rewrite get_op_output_keys_app in *.
rewrite get_op_output_keys_defn in *.
rewrite get_op_output_keys_app in *.
rewrite get_op_output_keys_defn in *.
Admitted.

Lemma NoDup_get_op_input_keys_In_2_3 : forall xs ys zs k, NoDup (get_op_input_keys (xs ++ I k :: ys ++ O k :: zs)) -> In (I k) (xs ++ ys ++ zs) -> False.
Proof using.
intros.
rewrite get_op_input_keys_app in *.
rewrite get_op_input_keys_defn in *.
rewrite get_op_input_keys_app in *.
rewrite get_op_input_keys_defn in *.
match goal with | [ H : NoDup _ |- _ ] => apply NoDup_remove_2 in H end.
Admitted.

Lemma O_IRO_preserved_IU : forall xs ys k' ir, (forall k, In (O k) (xs ++ I k' :: ys) -> In (IRO k) (IRI k' :: IRU k' :: ir)) -> forall k, In (O k) (xs ++ ys) -> In (IRO k) ir.
Proof using.
intros.
eapply In_cons_neq.
-
eapply In_cons_neq.
+
eauto.
+
discriminate.
-
Admitted.

Lemma O_IRO_preserved : forall xs ys zs k' ir, NoDup (get_op_output_keys (xs ++ I k' :: ys ++ O k' :: zs)) -> (forall k, In (O k) (xs ++ I k' :: ys ++ O k' :: zs) -> In (IRO k) (IRI k' :: IRO k' :: ir)) -> forall k, In (O k) (xs ++ ys ++ zs) -> In (IRO k) ir.
Proof using.
intros.
eapply In_cons_neq.
-
eapply In_cons_neq.
+
eauto using In_cons_2_3.
+
discriminate.
-
intro.
find_inversion.
Admitted.

Lemma no_Ik_in_first2 : forall xs ys zs k, NoDup (get_op_input_keys (xs ++ I k :: ys ++ O k :: zs)) -> forall k', In (I k') (xs ++ ys) -> k <> k'.
Proof using.
intros.
rewrite get_op_input_keys_app in *.
rewrite get_op_input_keys_defn in *.
match goal with | [ H : NoDup (_ ++ _ :: _) |- _ ] => apply NoDup_remove_2 in H end.
rewrite get_op_input_keys_app in *.
intro.
subst.
Admitted.

Lemma IRO_O_preserved_IU : forall xs ys k' ir, (forall k, In (IRO k) (IRI k' :: IRU k' :: ir) -> In (O k) (xs ++ I k' :: ys)) -> forall k, In (IRO k) ir -> In (O k) (xs ++ ys).
Proof using.
intros.
Admitted.

Lemma IRO_O_preserved : forall xs ys zs k' ir, (~ In k' (get_IR_output_keys ir)) -> (forall k, In (IRO k) (IRI k' :: IRO k' :: ir) -> In (O k) (xs ++ I k' :: ys ++ O k' :: zs)) -> forall k, In (IRO k) ir -> In (O k) (xs ++ ys ++ zs).
Proof using.
intros.
eapply In_cons_2_3_neq; eauto using in_cons; try congruence.
intro.
find_inversion.
Admitted.

Lemma IRU_I_preserved_IU : forall xs ys k' ir, (~ In k' (get_IR_output_keys ir)) -> (forall k, In (IRU k) (IRI k' :: IRU k' :: ir) -> In (I k) (xs ++ I k' :: ys)) -> forall k, In (IRU k) ir -> In (I k) (xs ++ ys).
Proof using.
intros.
apply in_middle_reduce with (y := I k'); intuition.
find_inversion.
Admitted.

Lemma IRU_I_preserved : forall xs ys zs k' ir, (~ In k' (get_IR_output_keys ir)) -> (forall k, In (IRU k) (IRI k' :: IRO k' :: ir) -> In (I k) (xs ++ I k' :: ys ++ O k' :: zs)) -> forall k, In (IRU k) ir -> In (I k) (xs ++ ys ++ zs).
Proof using.
intros.
eapply In_cons_2_3_neq; eauto using in_cons; try congruence.
intro.
find_inversion.
Admitted.

Lemma in_before_before_preserved_IU : forall xs ys k ir, NoDup (get_op_input_keys (xs ++ I k :: ys)) -> (forall k1 k2, In (I k2) (xs ++ I k :: ys) -> before (O k1) (I k2) (xs ++ I k :: ys) -> before (IRO k1) (IRI k2) (IRI k :: IRU k :: ir)) -> forall k1 k2, In (I k2) (xs ++ ys) -> before (O k1) (I k2) (xs ++ ys) -> before (IRO k1) (IRI k2) ir.
Proof using.
intros.
simpl in *.
find_eapply_lem_hyp before_middle_insert.
-
find_eapply_lem_hyp in_middle_insert.
eapply_prop_hyp In (O k1); eauto.
intuition; try congruence.
-
intro.
find_inversion.
Admitted.

Lemma in_before_before_preserved : forall xs ys zs k ir, NoDup (get_op_input_keys (xs ++ I k :: ys ++ O k :: zs)) -> NoDup (get_op_output_keys (xs ++ I k :: ys ++ O k :: zs)) -> (forall k1 k2, In (I k2) (xs ++ I k :: ys ++ O k :: zs) -> before (O k1) (I k2) (xs ++ I k :: ys ++ O k :: zs) -> before (IRO k1) (IRI k2) (IRI k :: IRO k :: ir)) -> forall k1 k2, In (I k2) (xs ++ ys ++ zs) -> before (O k1) (I k2) (xs ++ ys ++ zs) -> before (IRO k1) (IRI k2) ir.
Proof using.
intros.
simpl in *.
find_copy_eapply_lem_hyp before_2_3_insert.
-
find_eapply_lem_hyp In_cons_2_3.
eapply_prop_hyp In (O k1); eauto.
intuition; try congruence.
find_inversion.
find_copy_eapply_lem_hyp before_In.
exfalso.
eauto using NoDup_get_op_output_keys_In_2_3.
-
intro.
find_inversion.
eauto using NoDup_get_op_input_keys_In_2_3.
-
Admitted.

Lemma in_before_preserved_IU : forall xs ys k', ~ acknowledged_op k' (xs ++ ys) -> (forall k, In (O k) (xs ++ I k' :: ys) -> before (I k) (O k) (xs ++ I k' :: ys)) -> forall k, In (O k) (xs ++ ys) -> before (I k) (O k) (xs ++ ys).
Proof using.
intros.
eapply before_middle_reduce.
-
eauto using in_middle_insert.
-
intro.
find_inversion.
Admitted.

Lemma in_before_preserved : forall xs ys zs k', NoDup (get_op_output_keys (xs ++ I k' :: ys ++ O k' :: zs)) -> (forall k, In (O k) (xs ++ I k' :: ys ++ O k' :: zs) -> before (I k) (O k) (xs ++ I k' :: ys ++ O k' :: zs)) -> forall k, In (O k) (xs ++ ys ++ zs) -> before (I k) (O k) (xs ++ ys ++ zs).
Proof using.
intros.
eapply before_2_3_reduce.
-
eauto using In_cons_2_3.
-
intro.
find_inversion.
eauto using NoDup_get_op_output_keys_In_2_3.
-
Admitted.

Lemma IRI_I_preserved_IU : forall xs ys k' ir, (~ In k' (get_IR_input_keys ir)) -> (forall k, In (IRI k) (IRI k' :: IRU k' :: ir) -> In (I k) (xs ++ I k' :: ys)) -> forall k, In (IRI k) ir -> In (I k) (xs ++ ys).
Proof using.
intros.
eapply in_middle_reduce.
-
auto with *.
-
intro.
find_inversion.
Admitted.

Lemma IRI_I_preserved : forall xs ys zs k' ir, (~ In k' (get_IR_input_keys ir)) -> (forall k, In (IRI k) (IRI k' :: IRO k' :: ir) -> In (I k) (xs ++ I k' :: ys ++ O k' :: zs)) -> forall k, In (IRI k) ir -> In (I k) (xs ++ ys ++ zs).
Proof using.
intros.
eapply In_cons_2_3_neq.
-
auto with *.
-
intro.
find_inversion.
eauto using get_IR_input_keys_complete.
-
Admitted.

Lemma subseq_get_op_input_keys : forall xs ys, subseq xs ys -> subseq (get_op_input_keys xs) (get_op_input_keys ys).
Proof using.
Admitted.

Lemma subseq_get_op_output_keys : forall xs ys, subseq xs ys -> subseq (get_op_output_keys xs) (get_op_output_keys ys).
Proof using.
Admitted.

Lemma acknowledge_all_ops_func_target_ext_strong : forall (l : list op) (t t' : list IR), (forall k : K, In (I k) l -> In (IRU k) t -> In (IRU k) t') -> (forall k : K, In (I k) l -> In (IRU k) t' -> In (IRU k) t) -> acknowledge_all_ops_func l t = acknowledge_all_ops_func l t'.
Proof using.
induction l; intros.
-
auto.
-
simpl.
repeat break_match; subst; simpl in *; intuition auto 10 using f_equal with *.
+
exfalso.
eauto.
+
exfalso.
Admitted.

Lemma IRU_not_O_preserved_IU : forall xs ys k' ir, (forall k, In (IRU k) (IRI k' :: IRU k' :: ir) -> ~ In (O k) (xs ++ I k' :: ys)) -> forall k, In (IRU k) (ir) -> ~ In (O k) (xs ++ ys).
Proof using.
intuition.
eapply H.
-
apply in_cons.
apply in_cons.
eauto.
-
Admitted.

Lemma IRU_not_O_preserved : forall xs ys zs k' ir, (forall k, In (IRU k) (IRI k' :: IRO k' :: ir) -> ~ In (O k) (xs ++ I k' :: ys ++ O k' :: zs)) -> forall k, In (IRU k) (ir) -> ~ In (O k) (xs ++ ys ++ zs).
Proof using.
intuition.
eapply H.
-
eauto with *.
-
Admitted.

Lemma IR_equivalent_acknowledge_all_ops_func : forall ir, good_trace ir -> forall l, (forall k, In (O k) l -> In (IRO k) ir) -> (forall k, In (IRO k) ir -> In (O k) l) -> (forall k, In (IRU k) ir -> In (I k) l) -> (forall k, In (IRU k) ir -> ~ In (O k) l) -> (forall k k', In (I k') l -> before (O k) (I k') l -> before (IRO k) (IRI k') ir) -> (forall k, In (O k) l -> before (I k) (O k) l) -> (forall k, In (IRI k) ir -> In (I k) l) -> NoDup (get_op_input_keys l) -> NoDup (get_IR_input_keys ir) -> NoDup (get_op_output_keys l) -> NoDup (get_IR_output_keys ir) -> IR_equivalent (acknowledge_all_ops_func l ir) ir.
Proof using.
intros ir.
induction ir, good_trace using good_trace_ind; intros; try solve [simpl in *; intuition].
-
rewrite acknowledge_all_ops_func_target_nil; auto.
-
start.
eapply IR_equiv_trans.
+
apply op_equiv_AAOF_IR_equiv.
apply op_equivalent_all_Is_I_middle.
intros.
match goal with | [ H : context [before] |- _ ] => apply H end.
apply In_app_before; auto using op_eq_dec.
find_rewrite_lem get_op_input_keys_app.
rewrite get_op_input_keys_defn in *.
intro.
eapply NoDup_remove_2; eauto using in_or_app, get_op_input_keys_complete.
+
repeat rewrite app_ass.
rewrite acknowledge_all_ops_func_defn.
break_if.
*
constructor.
{
eapply IR_equiv_trans.
-
apply op_equiv_AAOF_IR_equiv.
rewrite <- app_ass.
eauto using op_equivalent_all_Is_O_middle, no_Ik_in_first2.
-
simpl.
constructor.
rewrite acknowledge_all_ops_func_target_ext with (t' := ir).
+
rewrite app_ass.
apply IHP; auto.
*
eauto using O_IRO_preserved.
*
eauto using IRO_O_preserved.
*
eauto using IRU_I_preserved.
*
eauto using IRU_not_O_preserved.
*
eauto using in_before_before_preserved.
*
eauto using in_before_preserved.
*
eauto using IRI_I_preserved.
*
eauto using subseq_NoDup, subseq_get_op_input_keys, subseq_2_3.
*
eauto using subseq_NoDup, subseq_get_op_output_keys, subseq_2_3.
+
simpl.
intuition congruence.
+
intuition.
}
*
{
break_if.
-
simpl in *.
intuition (try congruence).
exfalso.
eauto using get_IR_output_keys_complete_U.
-
exfalso.
apply n.
red.
intuition.
}
-
match goal with | [ H : good_trace (_ :: _) |- _ ] => simpl in H end.
break_and; subst.
match goal with | [ H : context [In (?c _) (_ :: ?c ?k' :: _) -> In _ ?l] |- _ ] => assert (In (I k') l) by firstorder; assert (forall x, before x (I k') l -> exists k, x = I k) by eauto using before_head_op end; repeat rewrite get_IR_input_keys_defn in *; repeat rewrite get_IR_output_keys_defn in *; repeat match goal with | [ H : NoDup (_ :: _) |- _ ] => invc H end.
find_copy_apply_lem_hyp in_split.
break_exists.
subst.
eapply IR_equiv_trans.
+
apply op_equiv_AAOF_IR_equiv.
apply op_equivalent_all_Is_I_middle.
intros.
match goal with | [ H : context [before] |- _ ] => apply H end.
apply In_app_before; auto using op_eq_dec.
find_rewrite_lem get_op_input_keys_app.
rewrite get_op_input_keys_defn in *.
intro.
eapply NoDup_remove_2; eauto using in_or_app, get_op_input_keys_complete.
+
rewrite acknowledge_all_ops_func_defn.
break_if.
*
exfalso.
intuition eauto using in_middle_insert, in_cons, in_eq, acknowledged_op_defn.
*
rewrite if_decider_true by intuition.
{
constructor.
constructor.
rewrite acknowledge_all_ops_func_target_ext_strong with (t' := ir).
-
apply IHP; auto.
+
eauto using O_IRO_preserved_IU.
+
eauto using IRO_O_preserved_IU.
+
eauto using IRU_I_preserved_IU.
+
eauto using IRU_not_O_preserved_IU.
+
eauto using in_before_before_preserved_IU.
+
eauto using in_before_preserved_IU.
+
eauto using IRI_I_preserved_IU.
+
eauto using subseq_NoDup, subseq_get_op_input_keys, subseq_middle.
+
eauto using subseq_NoDup, subseq_get_op_output_keys, subseq_middle.
-
simpl.
intuition (try congruence ).
find_inversion.
rewrite get_op_input_keys_app in *.
rewrite get_op_input_keys_defn in *.
exfalso.
repeat match goal with | [ H : In ?x (_ ++ ?x :: _) |- _ ] => clear H | [ H : In ?x (_ ++ _ :: _ ++ ?x :: _) |- _ ] => clear H end.
do_in_app.
eapply NoDup_remove_2; intuition eauto using in_or_app, get_op_input_keys_complete.
-
intros.
simpl.
intuition.
Admitted.

Theorem equivalent_intro : forall l ir, good_trace ir -> (forall k, In (O k) l -> In (IRO k) ir) -> (forall k, In (IRO k) ir -> In (O k) l) -> (forall k, In (IRU k) ir -> In (I k) l) -> (forall k k', In (I k') l -> before (O k) (I k') l -> before (IRO k) (IRI k') ir) -> (forall k, In (O k) l -> before (I k) (O k) l) -> (forall k, In (IRU k) ir -> ~ In (O k) l) -> NoDup (get_op_input_keys l) -> NoDup (get_IR_input_keys ir) -> NoDup (get_op_output_keys l) -> NoDup (get_IR_output_keys ir) -> equivalent l ir.
Proof using K_eq_dec.
intros.
red.
intuition.
exists (acknowledge_all_ops_func l ir).
intuition.
-
apply acknowledge_all_ops_func_correct.
-
apply IR_equivalent_acknowledge_all_ops_func; auto.
intros.
find_apply_lem_hyp good_trace_IRI_in; auto.
Admitted.

Lemma NoDup_get_op_input_keys_In_I : forall xs ys k, NoDup (get_op_input_keys (xs ++ I k :: ys)) -> In (I k) (xs ++ ys) -> False.
Proof using.
intros.
rewrite get_op_input_keys_app in *.
rewrite get_op_input_keys_defn in *.
do_in_app.
intuition; eapply NoDup_remove_2; eauto using get_op_input_keys_complete, in_or_app.
