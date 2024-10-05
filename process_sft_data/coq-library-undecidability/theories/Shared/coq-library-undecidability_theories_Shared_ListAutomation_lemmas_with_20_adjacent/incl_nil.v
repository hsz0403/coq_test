Require Export List Undecidability.Shared.Dec Undecidability.Shared.FilterFacts.
Export List.ListNotations.
Module ListAutomationNotations.
Notation "x 'el' L" := (In x L) (at level 70).
Notation "A '<<=' B" := (incl A B) (at level 70).
Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).
Notation "[ s | p ∈ A ',' P ]" := (map (fun p => s) (filter (fun p => Dec P) A)) (p pattern).
Notation "[ s | p ∈ A ]" := (map (fun p => s) A) (p pattern).
End ListAutomationNotations.
Import ListAutomationNotations.
Instance list_in_dec X (x : X) (A : list X) : eq_dec X -> dec (x el A).
Proof.
intros D.
apply in_dec.
exact D.
Ltac in_app n := (match goal with | [ |- In _ (_ ++ _) ] => match n with | 0 => idtac | 1 => eapply in_app_iff; left | S ?n => eapply in_app_iff; right; in_app n end | [ |- In _ (_ :: _) ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end end) || (repeat (try right; eapply in_app_iff; right)).
Ltac in_collect a := eapply in_map_iff; exists a; split; [ eauto | match goal with [ |- In _ (filter _ _) ] => eapply in_filter_iff; split; [ try (rewrite !in_prod_iff; repeat split) | eapply Dec_auto; repeat split; eauto ] | _ => try (rewrite !in_prod_iff; repeat split) end ].
Ltac inv_collect := repeat (match goal with | [ H : ?x el concat _ |- _ ] => eapply in_concat_iff in H as (? & ? & ?) | [ H : ?x el map _ _ |- _ ] => let x := fresh "x" in eapply in_map_iff in H as (x & ? & ?) | [ x : ?A * ?B |- _ ] => destruct x; subst | [ H : ?x el filter _ _ |- _ ] => let H' := fresh "H" in eapply in_filter_iff in H as (? & H' % to_dec) | [ H : ?x el list_prod _ _ |- _ ] => eapply in_prod_iff in H | [ H : _ el _ ++ _ |- _ ] => try eapply in_app_iff in H as [] | [H : _ el _ :: _ |- _ ] => destruct H end; intuition; subst).
Require Import Lia Arith.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Hint Extern 4 => match goal with |[ H: ?x el nil |- _ ] => destruct H end : core.
Hint Extern 4 => match goal with |[ H: False |- _ ] => destruct H |[ H: true=false |- _ ] => discriminate H |[ H: false=true |- _ ] => discriminate H end : core.
Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
Hint Resolve in_eq in_nil in_cons in_or_app : core.
Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app incl_nil : core.
Hint Resolve app_incl_l app_incl_R cons_incl incl_sing : core.
Hint Extern 4 (_ el map _ _) => eapply in_map_iff : core.
Hint Extern 4 (_ el filter _ _) => eapply filter_In : core.
Section Inclusion.
Variable X : Type.
Implicit Types A B : list X.
End Inclusion.
Require Import Setoid Morphisms.
Instance incl_preorder X : PreOrder (@incl X).
Proof.
constructor; hnf; unfold incl; auto.
Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Local Notation "A === B" := (equi A B) (at level 70).
Hint Unfold equi : core.
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

Instance list_in_dec X (x : X) (A : list X) : eq_dec X -> dec (x el A).
Proof.
intros D.
apply in_dec.
Admitted.

Lemma in_concat_iff A l (a:A) : a el concat l <-> exists l', a el l' /\ l' el l.
Proof.
induction l; cbn.
-
intuition.
now destruct H.
-
rewrite in_app_iff, IHl.
clear.
firstorder subst.
Admitted.

Lemma to_dec (P : Prop) `{dec P} : P <-> is_true (Dec P).
Proof.
Admitted.

Lemma app_incl_l X (A B C : list X) : A ++ B <<= C -> A <<= C.
Proof.
Admitted.

Lemma app_incl_R X (A B C : list X) : A ++ B <<= C -> B <<= C.
Proof.
Admitted.

Lemma cons_incl X (a : X) (A B : list X) : a :: A <<= B -> A <<= B.
Proof.
intros ? ? ?.
eapply H.
Admitted.

Lemma incl_sing X (a : X) A : a el A -> [a] <<= A.
Proof.
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

Lemma incl_rcons x A B : A <<= x::B -> ~ x el A -> A <<= B.
Proof.
intros C D y E.
Admitted.

Lemma incl_lrcons x A B : x::A <<= x::B -> ~ x el A -> A <<= B.
Proof.
intros C D y E.
assert (F: y el x::B) by auto.
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

Lemma incl_nil X (A : list X) : nil <<= A.
Proof.
intros x [].
