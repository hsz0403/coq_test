From Undecidability.FOL Require Import Util.FullTarski_facts Util.Syntax_facts Util.FullDeduction_facts.
From Undecidability.FOL Require Import ZF Reductions.PCPb_to_ZF Reductions.PCPb_to_minZF minZF Reductions.PCPb_to_ZFeq.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Require Import Equations.Equations.
Require Import Morphisms.
Local Notation vec := Vector.t.
Section Model.
Open Scope sem.
Context {V : Type} {I : interp V}.
Hypothesis M_ZF : forall rho, rho ⊫ ZFeq'.
Instance min_model : interp sig_empty _ V.
Proof.
split.
-
intros [].
-
now apply i_atom.
Defined.
Instance set_equiv_equiv' : Equivalence set_equiv.
Proof.
now apply set_equiv_equiv.
Instance set_equiv_elem' : Proper (set_equiv ==> set_equiv ==> iff) set_elem.
Proof.
now apply set_equiv_elem.
Instance set_equiv_sub' : Proper (set_equiv ==> set_equiv ==> iff) set_sub.
Proof.
now apply set_equiv_sub.
Instance equiv_union' : Proper (set_equiv ==> set_equiv) union.
Proof.
now apply equiv_union.
Instance equiv_power' : Proper (set_equiv ==> set_equiv) power.
Proof.
now apply equiv_power.
End Model.

Lemma min_axioms' (rho : nat -> V) : rho ⊫ minZFeq'.
Proof.
intros A [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn.
-
now apply set_equiv_equiv.
-
now apply set_equiv_equiv.
-
now apply set_equiv_equiv.
-
intros x x' y y' Hx Hy.
now apply set_equiv_elem.
-
intros x y H1 H2.
now apply M_ext.
-
exists ∅.
apply (@M_ZF rho ax_eset).
firstorder.
-
intros x y.
exists ({x; y}).
apply (@M_ZF rho ax_pair).
firstorder.
-
intros x.
exists (⋃ x).
apply (@M_ZF rho ax_union).
firstorder.
-
intros x.
exists (PP x).
apply (@M_ZF rho ax_power).
firstorder.
-
exists ω.
split.
split.
+
exists ∅.
split.
apply (@M_ZF rho ax_eset).
firstorder.
apply (@M_ZF rho ax_om1).
firstorder.
+
intros x Hx.
exists (σ x).
split.
2: apply (@M_ZF rho ax_om1); firstorder.
intros y.
now apply sigma_el.
+
intros x [H1 H2].
apply (@M_ZF rho ax_om2); cbn.
auto 12.
split.
*
destruct H1 as (e & E1 & E2).
change (set_elem ∅ x).
enough (set_equiv ∅ e) as -> by assumption.
apply M_ext; trivial.
all: intros y Hy; exfalso; try now apply E1 in Hy.
apply (@M_ZF rho ax_eset) in Hy; trivial.
unfold ZFeq', ZF'.
auto 8.
*
intros d (s & S1 & S2) % H2.
change (set_elem (σ d) x).
enough (set_equiv (σ d) s) as -> by assumption.
apply M_ext; trivial.
all: intros y; rewrite sigma_el; trivial; apply S1.
