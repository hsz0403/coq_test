From Undecidability.FOL Require Import Util.FullTarski_facts Util.Syntax_facts Util.FullDeduction_facts.
From Undecidability.FOL Require Import ZF Reductions.PCPb_to_ZF binZF Util.sig_bin.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Require Import Equations.Equations.
Require Import Morphisms.
Local Notation vec := Vector.t.
Existing Instance ZF_func_sig.
Existing Instance ZF_pred_sig.
Definition embed_t (t : term') : term := match t with | $x => $x | func f ts => False_rect term f end.
Fixpoint embed {ff'} (phi : form sig_empty sig_binary _ ff') : form ff' := match phi with | atom P ts => atom elem (Vector.map embed_t ts) | bin b phi psi => bin b (embed phi) (embed psi) | quant q phi => quant q (embed phi) | ⊥ => ⊥ end.
Definition sshift {Σ_funcs : funcs_signature} k : nat -> term := fun n => match n with 0 => $0 | S n => $(1 + k + n) end.
Fixpoint rm_const_tm (t : term) : form' := match t with | var n => $0 ≡' var (S n) | func eset _ => is_eset $0 | func pair v => let v' := Vector.map rm_const_tm v in ∃ (Vector.hd v')[sshift 1] ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 2] ∧ is_pair $1 $0 $2 | func union v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_union $0 $1 | func power v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_power $0 $1 | func omega v => is_om $0 end.
Fixpoint rm_const_fm {ff : falsity_flag} (phi : form) : form' := match phi with | ⊥ => ⊥ | bin bop phi psi => bin sig_empty _ bop (rm_const_fm phi) (rm_const_fm psi) | quant qop phi => quant qop (rm_const_fm phi) | atom elem v => let v' := Vector.map rm_const_tm v in ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ∈'$0 | atom equal v => let v' := Vector.map rm_const_tm v in ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ≡' $0 end.
Derive Signature for vec.
From Undecidability.FOL Require Import Reductions.PCPb_to_ZFeq.
Section Model.
Open Scope sem.
Context {V : Type} {I : interp V}.
Hypothesis M_ZF : forall rho, rho ⊫ ZFeq'.
Instance min_model : interp sig_empty sig_binary V.
Proof.
split.
-
intros [].
-
intros [] v.
exact (@i_atom _ _ _ _ elem v).
Defined.
Notation "x ≈ y" := (forall z, (x ∈ z -> y ∈ z) /\ (y ∈ z -> x ∈ z)) (at level 35) : sem.
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
Arguments eq' : simpl never.
Ltac prv_all' x := apply AllI; edestruct (@nameless_equiv_all sig_empty) as [x ->]; cbn; rewrite ?eq_subst; cbn; subsimpl.
Ltac use_exists' H x := apply (ExE _ H); edestruct (@nameless_equiv_ex sig_empty) as [x ->]; cbn; rewrite ?eq_subst; cbn; subsimpl.
Local Ltac simpl_ex := rewrite ?eq_subst; subsimpl; try apply prv_ex_eq; try apply use_ex_eq; auto; rewrite ?eq_subst; cbn; subsimpl.
Local Ltac simpl_ex_in H := rewrite ?eq_subst in H; subsimpl_in H; try apply prv_ex_eq in H; try apply use_ex_eq in H; auto; rewrite ?eq_subst in H; cbn in H; subsimpl_in H.
Local Arguments is_om : simpl never.
Local Arguments is_inductive : simpl never.
Local Arguments inductive : simpl never.
Local Arguments is_om : simpl nomatch.
Section Deduction.
End Deduction.

Lemma prv_to_min_inductive { p : peirce } A n : binZF <<= A -> A ⊢ rm_const_fm (inductive $n) -> A ⊢ is_inductive $n.
Proof.
cbn.
intros HA HI.
apply CI.
-
apply CE1 in HI.
use_exists' HI x.
clear HI.
apply (ExI x).
cbn.
assert1 H.
apply CE in H as [H1 H2].
apply CI; trivial.
change (∃ $0 ≡' ↑ n ∧ x`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ x`[↑] ∈' $0) in H2.
now simpl_ex_in H2.
-
apply CE2 in HI.
prv_all' x.
apply (AllE x) in HI.
cbn in HI.
simpl_ex_in HI.
change (∃ $0 ≡' ↑ n ∧ x`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ x`[↑] ∈' $0) in HI.
simpl_ex_in HI.
rewrite imps in *.
use_exists' HI y.
clear HI.
assert1 H.
apply (ExI y).
cbn.
subsimpl.
apply CI.
+
apply CE1 in H.
use_exists' H a.
clear H.
assert1 H.
apply CE in H as [H1 H2].
simpl_ex_in H1.
prv_all' b.
apply (AllE b) in H2.
cbn in H2.
subsimpl_in H2.
eapply iff_equiv; try apply H2; try tauto.
intros B HB.
clear H2.
eapply Weak in H1; try apply HB.
split; intros H2.
*
use_exists' H1 z.
clear H1.
assert1 H.
apply CE in H as [H H'].
apply prv_ex_eq in H; try rewrite <- HB; auto.
cbn in H.
subsimpl_in H.
rewrite ?eq_subst in H.
cbn in H.
subsimpl_in H.
apply prv_ex_eq in H; try rewrite <- HB; auto.
cbn in H.
subsimpl_in H.
eapply Weak in H2.
apply (DE H2).
3: auto.
--
apply (ExI x).
cbn.
subsimpl.
apply CI; auto.
apply (AllE x) in H'.
cbn in H'.
subsimpl_in H'.
apply CE2 in H'.
eapply IE.
apply (Weak H'); auto.
apply DI1.
rewrite ?eq_subst.
cbn.
subsimpl.
apply minZF_refl.
rewrite <- HB.
auto 6.
--
apply (ExI z).
cbn.
subsimpl.
apply CI.
++
apply (AllE z) in H'.
cbn in H'.
subsimpl_in H'.
apply CE2 in H'.
eapply IE.
apply (Weak H'); auto.
apply DI2.
rewrite ?eq_subst.
cbn.
subsimpl.
apply minZF_refl.
rewrite <- HB.
auto 6.
++
apply (AllE b) in H.
cbn in H.
subsimpl_in H.
apply CE2 in H.
eapply IE.
apply (Weak H); auto.
rewrite ?eq_subst.
cbn.
subsimpl.
apply DI2.
auto.
*
use_exists' H1 z.
clear H1.
assert1 H.
apply CE in H as [H H'].
apply prv_ex_eq in H; try rewrite <- HB; auto.
cbn in H.
subsimpl_in H.
rewrite ?eq_subst in H.
cbn in H.
subsimpl_in H.
apply prv_ex_eq in H; try rewrite <- HB; auto.
cbn in H.
subsimpl_in H.
eapply Weak in H2.
use_exists' H2 c.
2: auto.
clear H2.
assert1 H1.
apply CE in H1 as [H1 H2].
apply (AllE c) in H'.
cbn in H'.
subsimpl_in H'.
apply CE1 in H'.
eapply Weak in H'.
apply (IE H') in H1.
2: auto.
clear H'.
apply (DE H1).
--
apply DI1.
eapply minZF_elem.
rewrite <- HB, HA.
auto 8.
3: apply (Weak H2); auto.
apply minZF_refl.
rewrite <- HB, HA.
auto 8.
rewrite ?eq_subst.
cbn.
subsimpl.
auto.
--
apply DI2.
apply (AllE b) in H.
cbn in H.
subsimpl_in H.
apply CE1 in H.
eapply DE'.
rewrite ?eq_subst.
cbn.
subsimpl.
rewrite ?eq_subst in H.
cbn in H.
subsimpl_in H.
eapply IE.
apply (Weak H).
auto.
eapply minZF_elem.
rewrite <- HB, HA.
auto 8.
3: apply (Weak H2); auto.
2: auto.
apply minZF_refl.
rewrite <- HB, HA.
auto 8.
+
apply CE2 in H.
change (∃ $0 ≡' ↑ n ∧ y`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ y`[↑] ∈' $0) in H.
now simpl_ex_in H.
