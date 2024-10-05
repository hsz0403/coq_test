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

Lemma lsteps_cons_nil s S: star lstep (s :: S) nil -> False.
Proof.
intros.
remember (s :: S) as S'.
remember nil as T.
revert S s HeqS' HeqT.
induction H.
-
intros; subst; discriminate.
-
intros; subst.
Admitted.

Lemma lstep_nil_cons S: lstep nil S -> False.
Proof.
intros H.
Admitted.

Lemma lsteps_nil_cons s S: star lstep nil (s :: S) -> False.
Proof.
intros H.
inv H.
Admitted.

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
Admitted.

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
Admitted.

Lemma normal_lstep_in A: Normal lstep A -> forall x, In x A -> Normal R x.
Proof.
induction A; cbn; intuition; subst; eauto.
intros ? H1.
eapply H.
constructor.
eassumption.
eapply IHA; eauto.
intros ? H2.
eapply H.
Admitted.

Lemma normal_in_lstep A: (forall x, In x A -> Normal R x) -> Normal lstep A.
Proof.
induction A; cbn; intuition.
-
intros ? H1.
inv H1.
-
intros ? H1.
inv H1.
eapply H; eauto.
Admitted.

Lemma lstep_normal_cons_l a A: Normal lstep (a :: A) -> Normal R a.
Proof.
intros ? ? ?.
Admitted.

Lemma lstep_normal_cons_r a A: Normal lstep (a :: A) -> Normal lstep A.
Proof.
intros ? ? ?.
Admitted.

Lemma lstep_normal_cons a A: Normal R a -> Normal lstep A -> Normal lstep (a :: A).
Proof.
intros ? ? ? ?.
Admitted.

Lemma equiv_lstep_cons_inv s t S T: equiv lstep (s :: S) (t :: T) -> equiv R s t /\ equiv lstep S T.
Proof.
intros H.
remember (s :: S) as S'.
remember (t :: T) as T'.
revert s t S T HeqS' HeqT'.
induction H; intros.
-
subst.
injection HeqT' as ??; subst; intuition.
-
subst.
inv H.
+
destruct x'.
eapply lstep_cons_nil in H1 as [].
edestruct IHstar; eauto.
inv H1.
*
intuition.
transitivity x; eauto.
*
intuition.
transitivity x'; eauto.
+
destruct x'.
eapply lstep_nil_cons in H1 as [].
edestruct IHstar; eauto.
inv H1; intuition.
*
transitivity x; eauto.
*
Admitted.

Lemma not_equiv_lstep_nil_cons a A: ~ equiv lstep nil (a :: A).
Proof.
Admitted.

Lemma list_equiv_ind (P: list X -> list X -> Prop): P nil nil -> (forall s t S T, equiv R s t -> equiv lstep S T -> P S T -> P (s :: S) (t :: T)) -> forall S T, equiv lstep S T -> P S T.
Proof.
intros B IH S T H; induction S in T, H |-*; destruct T; eauto.
-
exfalso; eapply not_equiv_lstep_nil_cons; eauto.
-
exfalso; eapply not_equiv_lstep_nil_cons; symmetry; eauto.
-
eapply equiv_lstep_cons_inv in H as (? & ?).
Admitted.

Lemma lstep_normal_nil: Normal lstep nil.
Proof.
intros ? H; inv H.
