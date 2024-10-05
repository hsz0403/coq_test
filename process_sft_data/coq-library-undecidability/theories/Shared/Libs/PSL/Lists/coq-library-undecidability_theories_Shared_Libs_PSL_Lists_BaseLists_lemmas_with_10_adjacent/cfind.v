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

Lemma list_cycle (X : Type) (A : list X) x : x::A <> A.
Proof.
intros B.
assert (C: |x::A| <> |A|) by (cbn; lia).
apply C.
Admitted.

Instance list_in_dec X (x : X) (A : list X) : eq_dec X -> dec (x el A).
Proof.
intros D.
apply in_dec.
Admitted.

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
Admitted.

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
Admitted.

Lemma list_exists_DM X A (p : X -> Prop) : (forall x, dec (p x)) -> ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof.
intros D E.
destruct (find (fun x => Dec (p x)) A) eqn:Eq.
+
apply find_some in Eq as [? ?%Dec_true].
eauto.
+
exfalso.
apply E.
intros.
Admitted.

Lemma list_exists_not_incl (X: eqType) (A B : list X) : ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
intros E.
apply list_exists_DM; auto.
intros F.
apply E.
intros x G.
Admitted.

Lemma list_cc X (p : X -> Prop) A : (forall x, dec (p x)) -> (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
intros D E.
destruct (cfind A p) as [[x [F G]]|F].
-
eauto.
-
exfalso.
destruct E as [x [G H]].
Admitted.

Lemma in_sing x y : x el [y] -> x = y.
Proof.
cbn.
intros [[]|[]].
Admitted.

Lemma in_cons_neq x y A : x el y::A -> x <> y -> x el A.
Proof.
cbn.
Admitted.

Lemma not_in_cons x y A : ~ x el y :: A -> x <> y /\ ~ x el A.
Proof.
Admitted.

Lemma disjoint_forall A B : disjoint A B <-> forall x, x el A -> ~ x el B.
Proof.
split.
-
intros D x E F.
apply D.
exists x.
auto.
-
intros D [x [E F]].
Admitted.

Lemma disjoint_symm A B : disjoint A B -> disjoint B A.
Proof.
Admitted.

Lemma cfind X A (p: X -> Prop) (p_dec: forall x, dec (p x)) : {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
destruct (find (fun x => Dec (p x)) A) eqn:E.
-
apply find_some in E.
firstorder.
-
right.
intros.
eapply find_none in E; eauto.
