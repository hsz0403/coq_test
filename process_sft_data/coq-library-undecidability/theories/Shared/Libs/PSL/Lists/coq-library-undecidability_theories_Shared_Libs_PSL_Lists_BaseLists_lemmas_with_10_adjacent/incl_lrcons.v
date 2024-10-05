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

Lemma disjoint_nil' A : disjoint A nil.
Proof.
Admitted.

Lemma disjoint_cons x A B : disjoint (x::A) B <-> ~ x el B /\ disjoint A B.
Proof.
split.
-
intros D.
split.
+
intros E.
apply D.
eauto.
+
intros [y [E F]].
apply D.
eauto.
-
intros [D E] [y [[F|F] G]].
+
congruence.
+
apply E.
Admitted.

Lemma disjoint_app A B C : disjoint (A ++ B) C <-> disjoint A C /\ disjoint B C.
Proof.
split.
-
intros D.
split.
+
intros [x [E F]].
eauto 6.
+
intros [x [E F]].
eauto 6.
-
intros [D E] [x [F G]].
Admitted.

Lemma incl_nil X (A : list X) : nil <<= A.
Proof.
Admitted.

Lemma incl_map X Y A B (f : X -> Y) : A <<= B -> map f A <<= map f B.
Proof.
intros D y E.
apply in_map_iff in E as [x [E E']].
subst y.
apply in_map_iff.
Admitted.

Lemma incl_nil_eq A : A <<= nil -> A=nil.
Proof.
intros D.
destruct A as [|x A].
-
reflexivity.
-
exfalso.
apply (D x).
Admitted.

Lemma incl_shift x A B : A <<= B -> x::A <<= x::B.
Proof.
Admitted.

Lemma incl_lcons x A B : x::A <<= B <-> x el B /\ A <<= B.
Proof.
split.
-
intros D.
split; hnf; auto.
-
Admitted.

Lemma incl_sing x A y : x::A <<= [y] -> x = y /\ A <<= [y].
Proof.
rewrite incl_lcons.
intros [D E].
apply in_sing in D.
Admitted.

Lemma incl_rcons x A B : A <<= x::B -> ~ x el A -> A <<= B.
Proof.
intros C D y E.
Admitted.

Lemma incl_app_left A B C : A ++ B <<= C -> A <<= C /\ B <<= C.
Proof.
Admitted.

Instance incl_preorder X : PreOrder (@incl X).
Proof.
Admitted.

Instance equi_Equivalence X : Equivalence (@equi X).
Proof.
Admitted.

Instance incl_equi_proper X : Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof.
hnf.
intros A B D.
hnf.
Admitted.

Instance cons_incl_proper X x : Proper (@incl X ==> @incl X) (@cons X x).
Proof.
hnf.
Admitted.

Instance cons_equi_proper X x : Proper (@equi X ==> @equi X) (@cons X x).
Proof.
hnf.
Admitted.

Instance in_incl_proper X x : Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
intros A B D.
hnf.
Admitted.

Instance in_equi_proper X x : Proper (@equi X ==> iff) (@In X x).
Proof.
intros A B D.
Admitted.

Instance app_incl_proper X : Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof.
intros A B D A' B' E.
Admitted.

Instance app_equi_proper X : Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof.
hnf.
intros A B D.
hnf.
intros A' B' E.
Admitted.

Lemma incl_lrcons x A B : x::A <<= x::B -> ~ x el A -> A <<= B.
Proof.
intros C D y E.
assert (F: y el x::B) by auto.
destruct F as [F|F]; congruence.
