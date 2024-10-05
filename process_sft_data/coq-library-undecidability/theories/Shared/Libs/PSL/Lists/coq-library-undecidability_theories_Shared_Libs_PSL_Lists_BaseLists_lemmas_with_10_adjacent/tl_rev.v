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

Lemma map_eq_nil (Y Z: Type) (f: Y->Z) (l: list Y) : map f l = nil -> l = nil.
Proof.
intros.
destruct l; cbn in *.
reflexivity.
Admitted.

Lemma map_eq_nil' (Y Z: Type) (f: Y->Z) (l: list Y) : nil = map f l -> l = nil.
Proof.
Admitted.

Lemma map_eq_cons (A B: Type) (f: A->B) (xs: list A) (y: B) (ys: list B) : map f xs = y :: ys -> exists x xs', xs = x :: xs' /\ y = f x /\ ys = map f xs'.
Proof.
Admitted.

Lemma map_eq_cons' (A B: Type) (f: A -> B) (xs: list A) (y: B) (ys: list B) : y :: ys = map f xs -> exists x xs', xs = x :: xs' /\ y = f x /\ ys = map f xs'.
Proof.
Admitted.

Lemma map_eq_app (A B: Type) (f: A -> B) (ls : list A) (xs ys : list B) : map f ls = xs ++ ys -> exists ls1 ls2, ls = ls1 ++ ls2 /\ xs = map f ls1 /\ ys = map f ls2.
Proof.
revert xs ys.
induction ls; intros; cbn in *.
-
symmetry in H.
apply app_eq_nil in H as (->&->).
exists nil, nil.
cbn.
tauto.
-
destruct xs; cbn in *.
+
exists nil.
eexists.
repeat split.
cbn.
now subst.
+
inv H.
specialize IHls with (1 := H2) as (ls1&ls2&->&->&->).
repeat econstructor.
2: instantiate (1 := a :: ls1).
Admitted.

Lemma rev_eq_cons (A: Type) (ls: list A) (x : A) (xs: list A) : rev ls = x :: xs -> ls = rev xs ++ [x].
Proof.
intros H.
rewrite <- rev_involutive at 1.
rewrite H.
cbn.
Admitted.

Lemma map_injective (X Y: Type) (f: X -> Y) : (forall x y, f x = f y -> x = y) -> forall xs ys, map f xs = map f ys -> xs = ys.
Proof.
intros HInj.
hnf.
intros x1.
induction x1 as [ | x x1' IH]; intros; cbn in *.
-
now apply map_eq_nil' in H.
-
Admitted.

Instance map_ext_proper A B: Proper (@ pointwise_relation A B (@eq B) ==> (@eq (list A)) ==> (@eq (list B))) (@map A B).
Proof.
intros f f' Hf a ? <-.
Admitted.

Lemma tl_map (A B: Type) (f: A -> B) (xs : list A) : tl (map f xs) = map f (tl xs).
Proof.
Admitted.

Lemma tl_app (A: Type) (xs ys : list A) : xs <> nil -> tl (xs ++ ys) = tl xs ++ ys.
Proof.
Admitted.

Lemma hd_map (A B: Type) (f: A -> B) (xs : list A) (a : A) : hd (f a) (map f xs) = f (hd a xs).
Proof.
Admitted.

Lemma hd_app (A: Type) (xs ys : list A) a : xs <> nil -> hd a (xs ++ ys) = hd a xs.
Proof.
intros H.
destruct xs; auto.
Admitted.

Lemma hd_rev (A: Type) (xs : list A) (a : A) : hd a (rev xs) = last xs a.
Proof.
induction xs; cbn; auto.
destruct xs; cbn; auto.
rewrite hd_app.
now apply IHxs.
Admitted.

Lemma tl_rev (A: Type) (xs : list A) : tl (rev xs) = rev (removelast xs).
Proof.
induction xs; cbn; auto.
destruct xs; cbn in *; auto.
rewrite tl_app; cbn in *.
-
now rewrite IHxs.
-
intros (H1&H2) % app_eq_nil; inv H2.
