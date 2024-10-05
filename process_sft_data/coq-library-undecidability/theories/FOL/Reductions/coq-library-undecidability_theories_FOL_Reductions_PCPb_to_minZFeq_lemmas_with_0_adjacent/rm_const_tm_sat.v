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

Lemma rm_const_tm_sat (rho : nat -> V) (t : term) x : (x .: rho) ⊨ embed (rm_const_tm t) <-> set_equiv x (eval rho t).
Proof.
induction t in x |- *; try destruct F; cbn; split; try rewrite (vec_inv1 v); try rewrite (vec_inv2 v); cbn.
-
tauto.
-
tauto.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
intros H.
apply M_ext; trivial; intros y Hy; exfalso; intuition.
now apply M_eset in Hy.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
change (set_equiv x ∅ -> forall d : V, set_elem d x -> False).
intros H d.
rewrite H.
now apply M_eset.
-
intros (y & Hy & z & Hz & H).
rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
rewrite embed_sshift, sat_sshift2, IH in Hz; try apply in_hd_tl.
apply M_ext; trivial.
+
intros a Ha % H.
apply M_pair; trivial.
rewrite <- Hy, <- Hz.
tauto.
+
intros a Ha % M_pair; trivial.
apply H.
rewrite <- Hy, <- Hz in Ha.
tauto.
-
exists (eval rho (Vector.hd v)).
rewrite embed_sshift, sat_sshift1, IH; try apply in_hd.
split; try reflexivity.
exists (eval rho (Vector.hd (Vector.tl v))).
rewrite embed_sshift, sat_sshift2, IH; try apply in_hd_tl.
split; try reflexivity.
change (forall d, (set_elem d x -> d ≡ eval rho (Vector.hd v) \/ d ≡ eval rho (Vector.hd (Vector.tl v))) /\ (d ≡ eval rho (Vector.hd v) \/ d ≡ eval rho (Vector.hd (Vector.tl v)) -> set_elem d x)).
intros d.
rewrite H.
now apply M_pair.
-
intros (y & Hy & H).
rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
change (set_equiv x (union (eval rho (Vector.hd v)))).
rewrite <- Hy.
apply M_ext; trivial.
+
intros z Hz % H.
now apply M_union.
+
intros z Hz % M_union; trivial.
now apply H.
-
exists (eval rho (Vector.hd v)).
rewrite embed_sshift, sat_sshift1, IH; try apply in_hd.
split; try reflexivity.
change (forall d, (set_elem d x -> exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) /\ ((exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) -> set_elem d x)).
intros d.
rewrite H.
now apply M_union.
-
intros (y & Hy & H).
rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
change (set_equiv x (power (eval rho (Vector.hd v)))).
rewrite <- Hy.
apply M_ext; trivial.
+
intros z Hz.
apply M_power; trivial.
unfold set_sub.
now apply H.
+
intros z Hz.
now apply H, M_power.
-
exists (eval rho (Vector.hd v)).
rewrite embed_sshift, sat_sshift1, IH; try apply in_hd.
split; try reflexivity.
change (forall d, (set_elem d x -> d ⊆ eval rho (Vector.hd v)) /\ (d ⊆ eval rho (Vector.hd v) -> set_elem d x)).
intros d.
rewrite H.
now apply M_power.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
intros [H1 H2].
apply M_ext; trivial.
+
unfold set_sub.
apply H2.
apply (inductive_sat_om rho).
+
unfold set_sub.
apply M_om2; trivial.
apply inductive_sat with rho.
apply H1.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
split.
+
change ((exists d : V, (forall d0 : V, d0 ∈ d -> False) /\ set_elem d x) /\ (forall d : V, set_elem d x -> exists d0 : V, (forall d1 : V, (d1 ∈ d0 -> d1 ∈ d \/ d1 ≡ d) /\ (d1 ∈ d \/ d1 ≡ d -> d1 ∈ d0)) /\ set_elem d0 x)).
setoid_rewrite H.
apply (inductive_sat_om rho).
+
intros d Hd.
change (set_sub x d).
rewrite H.
unfold set_sub.
apply M_om2; trivial.
apply inductive_sat with rho.
apply Hd.
