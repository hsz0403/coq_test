Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Section Lindenbaum.
Context {A: Type} (CA: Countable A) (init: Ensemble A) (P: Ensemble A -> Prop).
Fixpoint LindenbaumChain (n: nat): Ensemble A := match n with | 0 => init | S n => fun a => LindenbaumChain n a \/ CA a n /\ P (Union _ (LindenbaumChain n) (Singleton _ a)) end.
Definition LindenbaumConstruction: Ensemble A := fun a => exists n, LindenbaumChain n a.
Hypothesis H_init: P init.
End Lindenbaum.
Definition Lindenbaum_preserves {A: Type} (P: Ensemble A -> Prop): Prop := forall (CA: Countable A) init, P init -> P (LindenbaumConstruction CA init P).
Definition Lindenbaum_ensures {A: Type} (P cP: Ensemble A -> Prop): Prop := forall (CA: Countable A) init, P init -> cP (LindenbaumConstruction CA init P).
Definition Lindenbaum_constructable {A: Type} (P cP: Ensemble A -> Prop): Prop := forall Phi, P Phi -> exists Psi: sig cP, Included _ Phi (proj1_sig Psi) /\ P (proj1_sig Psi).

Lemma Lindenbaum_included_n_m: forall n m, n <= m -> Included _ (LindenbaumChain n) (LindenbaumChain m).
Proof.
intros.
induction H.
+
exact (fun x H => H).
+
refine (fun x H => _ (IHle x H)).
clear.
unfold Ensembles.In; intros; simpl.
left.
auto.
