Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OSAGenerators.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.Extensions.Semantics.SemanticStable.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.ModalLogic.Semantics.Flat.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Class ModalBisJoin (worlds: Type) {R2: KM.Relation worlds} {J: Join worlds} := { KM_join_bis: forall m n, R2 m n -> (forall n1 n2, join n1 n2 n -> exists m1 m2, join m1 m2 m /\ R2 m1 n1 /\ R2 m2 n2) /\ (forall m1 m2, join m1 m2 m -> exists n1 n2, join n1 n2 n /\ R2 m1 n1 /\ R2 m2 n2) }.
Instance prod_KM_bis_J (A B: Type) (RA: KM.Relation A) (RB: KM.Relation B) (JA: Join A) (JB: Join B) {KM_bis_JA: ModalBisJoin A} {KM_bis_JB: ModalBisJoin B}: @ModalBisJoin (A * B) (RelProd RA RB) (@prod_Join _ _ JA JB).
Proof.
constructor.
intros [m1 m2] [n1 n2] [? ?].
pose proof (@KM_join_bis A _ _ KM_bis_JA m1 n1 H).
pose proof (@KM_join_bis B _ _ KM_bis_JB m2 n2 H0).
split.
+
intros [n11 n12] [n21 n22] [? ?].
destruct H1 as [? _].
destruct H2 as [? _].
specialize (H1 _ _ H3).
destruct H1 as [m11 [m21 [? [? ?]]]].
specialize (H2 _ _ H4).
destruct H2 as [m12 [m22 [? [? ?]]]].
exists (m11, m12), (m21, m22).
split; [| split]; split; auto.
+
intros [m11 m12] [m21 m22] [? ?].
destruct H1 as [_ ?].
destruct H2 as [_ ?].
specialize (H1 _ _ H3).
destruct H1 as [n11 [n21 [? [? ?]]]].
specialize (H2 _ _ H4).
destruct H2 as [n12 [n22 [? [? ?]]]].
exists (n11, n12), (n21, n22).
split; [| split]; split; auto.
Instance eq_bis_J (A: Type) (J: Join A): @ModalBisJoin A eq J.
Proof.
constructor.
intros; subst.
split; intros.
+
exists n1, n2; auto.
+
exists m1, m2; auto.

Instance eq_bis_J (A: Type) (J: Join A): @ModalBisJoin A eq J.
Proof.
constructor.
intros; subst.
split; intros.
+
exists n1, n2; auto.
+
exists m1, m2; auto.
