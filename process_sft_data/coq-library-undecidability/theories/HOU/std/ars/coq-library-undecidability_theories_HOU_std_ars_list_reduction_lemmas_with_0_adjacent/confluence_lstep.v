Set Implicit Arguments.
Require Import List Morphisms FinFun.
From Undecidability.HOU Require Import std.tactics std.ars.basic std.ars.confluence.
Import ListNotations.
Set Default Proof Using "Type".
Section ListRelations.
Variable (X : Type) (R: X -> X -> Prop).
Inductive lstep: list X -> list X -> Prop := | stepHead s s' A: R s s' -> lstep (s :: A) (s' :: A) | stepTail s A A': lstep A A' -> lstep (s :: A) (s :: A').
Hint Constructors lstep : core.
Global Instance lsteps_cons : Proper (star R ++> star lstep ++> star lstep) cons.
Proof.
intros ??; induction 1; intros ??; induction 1; eauto.
Hint Resolve confluence_lstep : core.
Hint Resolve lstep_normal_nil lstep_normal_cons_l lstep_normal_cons_r lstep_normal_cons : core.
Hint Resolve normal_lstep_in normal_in_lstep : core.
Global Instance equiv_lstep_cons_proper: Proper (equiv R ++> equiv lstep ++> equiv lstep) cons.
Proof.
intros ??; induction 1; intros ??; induction 1; eauto.
-
rewrite <-IHstar.
destruct H.
eauto.
symmetry.
eauto.
-
rewrite <-(IHstar x0 x0); try reflexivity.
destruct H.
eauto.
symmetry.
eauto.
-
rewrite <-IHstar0.
destruct H1.
eauto.
symmetry.
eauto.
End ListRelations.
Hint Constructors lstep : core.
Hint Resolve lstep_normal_nil lstep_normal_cons_l lstep_normal_cons_r lstep_normal_cons : core.
Hint Resolve confluence_lstep : core.
Hint Resolve normal_lstep_in normal_in_lstep : core.

Lemma confluence_lstep: confluent R -> confluent lstep.
Proof.
intros conf ?.
induction x; intros.
-
inv H.
inv H0.
exists nil; eauto.
inv H.
inv H1.
-
destruct y, z; try solve [exfalso; eapply lsteps_cons_nil; eauto].
eapply lsteps_cons_inv in H; eapply lsteps_cons_inv in H0.
intuition; destruct (IHx _ _ H2 H3) as [V].
destruct (conf _ _ _ H1 H) as [v].
exists (v :: V).
now rewrite H5, H0.
now rewrite H6, H4.
