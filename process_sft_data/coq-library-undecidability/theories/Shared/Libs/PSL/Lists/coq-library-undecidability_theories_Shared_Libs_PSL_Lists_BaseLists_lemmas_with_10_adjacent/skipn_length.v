From Undecidability.Shared.Libs.PSL Require Export Prelim EqDec.
Export List.ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).
Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Notation "A === B" := (equi A B) (at level 70).
Hint Unfold equi : core.
Hint Extern 4 => match goal with |[ H: ?x el nil |- _ ] => destruct H end : core.
Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
Instance list_in_dec X (x : X) (A : list X) : eq_dec X -> dec (x el A).
Proof.
intros D.
apply in_dec.
exact D.
Arguments cfind {X} A p {p_dec}.
Instance list_forall_dec X A (p : X -> Prop) : (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
intros p_dec.
destruct (find (fun x => Dec (~ p x)) A) eqn:Eq.
-
apply find_some in Eq as [H1 H0 %Dec_true]; right; auto.
-
left.
intros x E.
apply find_none with (x := x) in Eq.
apply dec_DN; auto.
auto.
Instance list_exists_dec X A (p : X -> Prop) : (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
intros p_dec.
destruct (find (fun x => Dec (p x)) A) eqn:Eq.
-
apply find_some in Eq as [H0 H1 %Dec_true].
firstorder.
-
right.
intros [x [E F]].
apply find_none with (x := x) in Eq; auto.
eauto.
Hint Resolve in_eq in_nil in_cons in_or_app : core.
Section Membership.
Variable X : Type.
Implicit Types (x y: X) (A B: list X).
Definition disjoint A B := ~ exists x, x el A /\ x el B.
End Membership.
Hint Resolve disjoint_nil disjoint_nil' : core.
Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app : core.
Hint Resolve incl_nil : core.
Section Inclusion.
Variable X : Type.
Implicit Types A B : list X.
End Inclusion.
Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop := forall x, x el A -> p x.
Instance incl_preorder X : PreOrder (@incl X).
Proof.
constructor; hnf; unfold incl; auto.
Instance equi_Equivalence X : Equivalence (@equi X).
Proof.
constructor; hnf; firstorder.
Instance incl_equi_proper X : Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof.
hnf.
intros A B D.
hnf.
firstorder.
Instance cons_incl_proper X x : Proper (@incl X ==> @incl X) (@cons X x).
Proof.
hnf.
apply incl_shift.
Instance cons_equi_proper X x : Proper (@equi X ==> @equi X) (@cons X x).
Proof.
hnf.
firstorder.
Instance in_incl_proper X x : Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
intros A B D.
hnf.
auto.
Instance in_equi_proper X x : Proper (@equi X ==> iff) (@In X x).
Proof.
intros A B D.
firstorder.
Instance app_incl_proper X : Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof.
intros A B D A' B' E.
auto.
Instance app_equi_proper X : Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof.
hnf.
intros A B D.
hnf.
intros A' B' E.
destruct D, E; auto.
Section Equi.
Variable X : Type.
Implicit Types A B : list X.
End Equi.
Instance map_ext_proper A B: Proper (@ pointwise_relation A B (@eq B) ==> (@eq (list A)) ==> (@eq (list B))) (@map A B).
Proof.
intros f f' Hf a ? <-.
induction a;cbn;congruence.

Instance app_equi_proper X : Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof.
hnf.
intros A B D.
hnf.
intros A' B' E.
Admitted.

Lemma equi_push x A : x el A -> A === x::A.
Proof.
Admitted.

Lemma equi_dup x A : x::A === x::x::A.
Proof.
Admitted.

Lemma equi_swap x y A: x::y::A === y::x::A.
Proof.
Admitted.

Lemma equi_shift x A B : x::A++B === A++x::B.
Proof.
split; intros y.
-
intros [D|D].
+
subst; auto.
+
apply in_app_iff in D as [D|D]; auto.
-
intros D.
apply in_app_iff in D as [D|D].
+
auto.
+
Admitted.

Lemma equi_rotate x A : x::A === A++[x].
Proof.
split; intros y; cbn.
-
intros [D|D]; subst; auto.
-
intros D.
apply in_app_iff in D as [D|D].
+
auto.
+
apply in_sing in D.
Admitted.

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
induction l; cbn.
-
intuition.
now destruct H.
-
rewrite in_app_iff, IHl.
firstorder subst.
Admitted.

Lemma app_comm_cons' (A : Type) (x y : list A) (a : A) : x ++ a :: y = (x ++ [a]) ++ y.
Proof.
rewrite <- app_assoc.
cbn.
Admitted.

Lemma skipn_nil (X : Type) (n : nat) : skipn n nil = @nil X.
Proof.
Admitted.

Lemma skipn_app (X : Type) (xs ys : list X) (n : nat) : n = (| xs |) -> skipn n (xs ++ ys) = ys.
Proof.
intros ->.
revert ys.
Admitted.

Lemma map_repeat (X Y : Type) (f : X -> Y) (n : nat) (a : X) : map f (repeat a n) = repeat (f a) n.
Proof.
Admitted.

Lemma repeat_add_app (X : Type) (m n : nat) (a : X) : repeat a (m + n) = repeat a m ++ repeat a n.
Proof.
Admitted.

Lemma repeat_S_cons (X : Type) (n : nat) (a : X) : a :: repeat a n = repeat a n ++ [a].
Proof.
replace (a :: repeat a n) with (repeat a (S n)) by trivial.
replace (S n) with (n+1) by lia.
rewrite repeat_add_app.
cbn.
Admitted.

Lemma repeat_app_eq (X : Type) (m n : nat) (a : X) : repeat a n ++ repeat a m = repeat a m ++ repeat a n.
Proof.
rewrite <- !repeat_add_app.
f_equal.
Admitted.

Lemma repeat_eq_iff (X : Type) (n : nat) (a : X) x : x = repeat a n <-> length x = n /\ forall y, y el x -> y = a.
Proof.
split.
{
intros ->.
split.
apply repeat_length.
apply repeat_spec.
}
{
revert x.
induction n; intros x (H1&H2); cbn in *.
-
destruct x; cbn in *; congruence.
-
destruct x; cbn in *; inv H1.
f_equal.
+
apply H2.
auto.
+
apply IHn.
auto.
Admitted.

Lemma rev_repeat (X : Type) (n : nat) (a : X) : rev (repeat a n) = repeat a n.
Proof.
apply repeat_eq_iff.
split.
-
rewrite rev_length.
rewrite repeat_length.
auto.
-
intros y Hx % in_rev.
Admitted.

Lemma concat_repeat_repeat (X : Type) (n m : nat) (a : X) : concat (repeat (repeat a n) m) = repeat a (m*n).
Proof.
induction m as [ | m' IHm]; cbn.
-
auto.
-
rewrite repeat_add_app.
f_equal.
Admitted.

Corollary skipn_repeat_add (X : Type) (n m : nat) (a : X) : skipn n (repeat a (n + m)) = repeat a m.
Proof.
rewrite repeat_add_app.
erewrite skipn_app; eauto.
symmetry.
Admitted.

Corollary skipn_repeat (X : Type) (n : nat) (a : X) : skipn n (repeat a n) = nil.
Proof.
rewrite <- (app_nil_r (repeat a n)).
erewrite skipn_app; eauto.
symmetry.
Admitted.

Lemma rev_eq_nil (Z: Type) (l: list Z) : rev l = nil -> l = nil.
Proof.
intros.
destruct l; cbn in *.
reflexivity.
symmetry in H.
Admitted.

Lemma skipn_length (X : Type) (n : nat) (xs : list X) : length (skipn n xs) = length xs - n.
Proof.
revert xs.
induction n; intros; cbn.
-
lia.
-
destruct xs; cbn; auto.
