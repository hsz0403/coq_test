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

Lemma lsteps_cons_inv s t S T: star lstep (s :: S) (t :: T) -> star R s t /\ star lstep S T.
Proof.
intros H.
remember (s :: S) as S'.
remember (t :: T) as T'.
revert s t S T HeqS' HeqT'.
induction H; intros.
-
subst.
injection HeqT' as ??; subst.
intuition.
-
subst.
inv H.
+
destruct (IHstar s' t S T); eauto.
+
destruct (IHstar s t A' T); eauto.
