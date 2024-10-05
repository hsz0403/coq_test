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

Lemma rm_const_sat (rho : nat -> V) (phi : form) : rho ⊨ phi <-> rho ⊨ embed (rm_const_fm phi).
Proof.
induction phi in rho |- *; try destruct P; try destruct b0; try destruct q; cbn.
1,4-6: intuition.
-
rewrite (vec_inv2 t).
cbn.
split.
+
intros H.
exists (eval rho (Vector.hd t)).
rewrite rm_const_tm_sat.
split; try reflexivity.
exists (eval rho (Vector.hd (Vector.tl t))).
now rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
+
intros (x & Hx & y & Hy & H).
apply rm_const_tm_sat in Hx.
change (set_elem (eval rho (Vector.hd t)) (eval rho (Vector.hd (Vector.tl t)))).
rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy.
now rewrite <- Hx, <- Hy.
-
rewrite (vec_inv2 t).
cbn.
split.
+
intros H.
exists (eval rho (Vector.hd t)).
rewrite rm_const_tm_sat.
split; try reflexivity.
exists (eval rho (Vector.hd (Vector.tl t))).
rewrite embed_sshift, sat_sshift1, rm_const_tm_sat.
split; trivial.
reflexivity.
+
intros (x & Hx & y & Hy & H).
apply rm_const_tm_sat in Hx.
change (set_equiv (eval rho (Vector.hd t)) (eval rho (Vector.hd (Vector.tl t)))).
rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy.
now rewrite <- Hx, <- Hy.
-
split; intros; intuition.
-
firstorder eauto.
