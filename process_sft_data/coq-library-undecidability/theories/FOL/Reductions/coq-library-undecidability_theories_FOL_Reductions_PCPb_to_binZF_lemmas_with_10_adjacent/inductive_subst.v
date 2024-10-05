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

Lemma prv_to_min_refl { p : peirce } : binZF ⊢ rm_const_fm ax_refl.
Proof.
prv_all' x.
repeat simpl_ex.
Admitted.

Lemma prv_to_min_sym { p : peirce } : binZF ⊢ rm_const_fm ax_sym.
Proof.
prv_all' x.
prv_all' y.
subsimpl.
apply II.
assert1 H.
use_exists' H a.
assert1 H'.
apply CE2 in H'.
use_exists' H' b.
repeat simpl_ex.
eapply minZF_trans; auto.
-
apply minZF_sym; auto.
eapply CE1.
auto.
-
eapply minZF_trans; auto.
apply minZF_sym; auto.
eapply CE2.
auto.
eapply CE1, Ctx.
Admitted.

Lemma prv_to_min_trans { p : peirce } : binZF ⊢ rm_const_fm ax_trans.
Proof.
prv_all' x.
prv_all' y.
prv_all' z.
repeat simpl_ex.
apply II.
repeat simpl_ex.
apply II.
repeat simpl_ex.
Admitted.

Lemma prv_to_min_elem { p : peirce } : binZF ⊢ rm_const_fm ax_eq_elem.
Proof.
prv_all' x.
prv_all' y.
prv_all' u.
prv_all' v.
repeat simpl_ex.
apply II.
repeat simpl_ex.
apply II.
repeat simpl_ex.
apply II.
repeat simpl_ex.
Admitted.

Lemma prv_to_min_ext { p : peirce } : binZF ⊢ rm_const_fm ax_ext.
Proof.
prv_all' x.
prv_all' y.
apply II.
apply II.
repeat simpl_ex.
apply minZF_ext; auto; prv_all' z; apply II.
-
assert3 H.
apply (AllE z) in H.
cbn in H.
subsimpl_in H.
repeat simpl_ex_in H.
rewrite imps in H.
repeat simpl_ex_in H.
apply (Weak H).
auto.
-
assert2 H.
apply (AllE z) in H.
cbn in H.
subsimpl_in H.
repeat simpl_ex_in H.
rewrite imps in H.
repeat simpl_ex_in H.
apply (Weak H).
Admitted.

Lemma prv_to_min_eset { p : peirce } : binZF ⊢ rm_const_fm ax_eset.
Proof.
prv_all' x.
simpl_ex.
apply II.
assert1 H.
use_exists' H y.
clear H.
eapply IE.
2: eapply CE2, Ctx; auto 1.
assert1 H.
apply CE1 in H.
apply (AllE x) in H.
cbn in H.
Admitted.

Lemma prv_to_min_pair { p : peirce } : binZF ⊢ rm_const_fm ax_pair.
Proof.
prv_all' x.
prv_all' y.
prv_all' z.
apply CI.
-
simpl_ex.
apply II.
assert1 H.
use_exists' H u.
clear H.
assert1 H.
apply CE in H as [H1 H2].
repeat simpl_ex_in H1.
apply (AllE z) in H1.
cbn in H1.
subsimpl_in H1.
apply CE1 in H1.
apply (IE H1) in H2.
apply (DE H2); [apply DI1 | apply DI2].
all: repeat simpl_ex.
-
assert (HP : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
apply (AllE y) in HP.
cbn in HP.
apply (AllE x) in HP.
cbn in HP.
use_exists' HP u.
clear HP.
apply II.
simpl_ex.
apply (ExI u).
cbn.
subsimpl.
apply CI.
+
repeat simpl_ex.
+
assert2 H.
apply (AllE z) in H.
cbn in H.
subsimpl_in H.
apply CE2 in H.
apply (IE H).
clear H.
eapply DE.
*
apply Ctx.
auto.
*
apply DI1.
assert1 H.
repeat simpl_ex_in H.
rewrite eq_subst.
cbn.
now subsimpl.
*
apply DI2.
assert1 H.
repeat simpl_ex_in H.
rewrite eq_subst.
cbn.
Admitted.

Lemma prv_to_min_union { p : peirce } : binZF ⊢ rm_const_fm ax_union.
Proof.
prv_all' x.
prv_all' y.
apply CI.
-
simpl_ex.
apply II.
assert1 H.
use_exists' H u.
clear H.
assert1 H.
apply CE in H as [H1 H2].
simpl_ex_in H1.
apply (AllE y) in H1.
cbn in H1.
subsimpl_in H1.
apply CE1 in H1.
apply (IE H1) in H2.
use_exists' H2 z.
apply (ExI z).
cbn.
subsimpl.
apply CI; repeat simpl_ex.
+
eapply CE1.
auto.
+
eapply CE2.
auto.
-
assert (HU : binZF ⊢ ax_union') by (apply Ctx; firstorder).
apply (AllE x) in HU.
cbn in HU.
use_exists' HU u.
apply II.
assert1 H.
use_exists' H z.
clear H.
assert1 H.
apply CE in H as [H1 H2].
repeat simpl_ex_in H1.
repeat simpl_ex_in H2.
simpl_ex.
apply (ExI u).
cbn.
subsimpl.
apply CI.
+
repeat simpl_ex.
+
assert3 Hu.
apply (AllE y) in Hu.
cbn in Hu.
subsimpl_in Hu.
apply CE2 in Hu.
apply (IE Hu).
apply (ExI z).
cbn.
subsimpl.
Admitted.

Lemma prv_to_min_power { p : peirce } : binZF ⊢ rm_const_fm ax_power.
Proof.
prv_all' x.
prv_all' y.
apply CI.
-
simpl_ex.
apply II.
assert1 H.
use_exists' H u.
clear H.
assert1 H.
apply CE in H as [H1 H2].
simpl_ex_in H1.
apply (AllE y) in H1.
cbn in H1.
subsimpl_in H1.
apply CE1 in H1.
apply (IE H1) in H2.
prv_all' z.
repeat simpl_ex.
apply II.
repeat simpl_ex.
apply imps.
apply (AllE z) in H2.
cbn in H2.
now subsimpl_in H2.
-
assert (HP : binZF ⊢ ax_power') by (apply Ctx; firstorder).
apply (AllE x) in HP.
cbn in HP.
use_exists' HP u.
clear HP.
apply II.
simpl_ex.
apply (ExI u).
cbn.
subsimpl.
apply CI.
+
simpl_ex.
apply Ctx.
auto.
+
assert2 H.
apply (AllE y) in H.
cbn in H.
subsimpl_in H.
apply CE2 in H.
apply (IE H).
clear H.
prv_all' z.
apply II.
assert2 H.
apply (AllE z) in H.
cbn in H.
subsimpl_in H.
repeat simpl_ex_in H.
rewrite imps in H.
repeat simpl_ex_in H.
apply (Weak H).
Admitted.

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
Admitted.

Lemma is_inductive_subst t sigma : (is_inductive t)[sigma] = is_inductive t`[sigma].
Proof.
cbn.
subsimpl.
Admitted.

Lemma is_om_subst t sigma : (is_om t)[sigma] = is_om t`[sigma].
Proof.
cbn.
subsimpl.
Admitted.

Lemma is_eset_sub { p : peirce } A x y : binZF <<= A -> A ⊢ is_eset x -> A ⊢ sub' x y.
Proof.
intros HA HE.
prv_all' z.
apply II, Exp, IE with (($0 ∈' x`[↑])[z..]).
-
change ((z ∈' x :: A) ⊢ (¬ $0 ∈' x`[↑])[z..]).
apply AllE, (Weak HE).
auto.
-
cbn.
subsimpl.
Admitted.

Lemma is_eset_unique { p : peirce } A x y : binZF <<= A -> A ⊢ is_eset x -> A ⊢ is_eset y -> A ⊢ x ≡' y.
Proof.
intros HA H1 H2.
Admitted.

Lemma prv_to_min_om1 { p : peirce } : binZF ⊢ rm_const_fm ax_om1.
Proof.
apply CI.
-
assert (HO : binZF ⊢ ax_om') by (apply Ctx; firstorder).
use_exists' HO o.
clear HO.
assert (HE : binZF ⊢ ax_eset') by (apply Ctx; firstorder).
eapply Weak in HE.
use_exists' HE e.
clear HE.
2: auto.
apply (ExI e).
cbn.
apply CI; auto.
apply (ExI o).
cbn.
subsimpl.
rewrite eq_sshift1.
apply CI; auto.
assert2 H.
unfold is_om in H at 2.
cbn in H.
apply CE1 in H.
rewrite is_inductive_subst in H.
cbn in H.
apply CE1 in H.
use_exists' H e'.
clear H.
assert1 H.
apply CE in H as [H1 H2].
eapply minZF_elem; auto; try eassumption.
2: apply minZF_refl; auto.
apply is_eset_unique; auto.
-
prv_all' x.
simpl_ex.
rewrite up_sshift1, eq_sshift1, !is_om_subst.
cbn.
apply II.
assert1 H.
use_exists' H o.
clear H.
assert1 H.
apply CE in H as [H1 H2].
unfold is_om in H1 at 3.
cbn in H1.
apply CE1 in H1.
unfold is_inductive in H1.
cbn in H1.
apply CE2 in H1.
apply (AllE x) in H1.
cbn in H1.
subsimpl_in H1.
apply (IE H1) in H2.
use_exists' H2 y.
clear H1 H2.
apply (ExI y).
cbn.
subsimpl.
apply CI.
+
assert (HP : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
apply (AllE x) in HP.
cbn in HP.
subsimpl_in HP.
apply (AllE x) in HP.
cbn in HP.
subsimpl_in HP.
eapply Weak in HP.
use_exists' HP s.
2: auto.
clear HP.
assert (HP : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
apply (AllE x) in HP.
cbn in HP.
subsimpl_in HP.
apply (AllE s) in HP.
cbn in HP.
subsimpl_in HP.
eapply Weak in HP.
use_exists' HP t.
2: auto.
clear HP.
apply (ExI t).
cbn.
subsimpl.
apply CI.
*
rewrite ?eq_subst.
cbn.
subsimpl.
apply prv_ex_eq; auto 7.
apply (ExI s).
cbn.
rewrite ?eq_subst.
cbn.
subsimpl.
apply CI; auto.
apply prv_ex_eq; auto 7.
cbn.
rewrite ?eq_subst.
cbn.
subsimpl.
apply prv_ex_eq; auto 7.
cbn.
rewrite ?eq_subst.
cbn.
subsimpl.
auto.
*
prv_all' z.
assert3 H.
apply CE1, (AllE z) in H.
cbn in H.
subsimpl_in H.
apply CE in H as [H1 H2].
apply CI; rewrite imps in *.
--
clear H2.
apply (DE H1); clear H1.
++
apply (ExI x).
cbn.
subsimpl.
apply CI; auto.
assert3 H.
apply (AllE x) in H.
cbn in H.
subsimpl_in H.
apply CE2 in H.
apply (IE H).
apply DI1.
rewrite ?eq_subst.
cbn.
subsimpl.
apply minZF_refl.
auto 8.
++
apply (ExI s).
cbn.
subsimpl.
apply CI.
**
assert3 H.
apply (AllE s) in H.
cbn in H.
subsimpl_in H.
apply CE2 in H.
apply (IE H).
apply DI2.
rewrite ?eq_subst.
cbn.
subsimpl.
apply minZF_refl.
auto 8.
**
assert4 H.
apply (AllE z) in H.
cbn in H.
subsimpl_in H.
apply CE2 in H.
apply (IE H).
apply DI1.
auto.
--
rewrite <- imps in H2.
eapply Weak in H2.
apply (IE H2).
2: auto.
clear H1 H2.
assert1 H.
use_exists' H a.
clear H.
assert1 H.
apply CE in H as [H1 H2].
assert3 H.
apply (AllE a) in H.
cbn in H.
subsimpl_in H.
apply CE1 in H.
apply (IE H) in H1.
clear H.
apply (DE H1).
**
apply DI1.
rewrite ?eq_subst.
cbn.
subsimpl.
eapply minZF_elem; auto 9.
2: apply (Weak H2); auto.
apply minZF_refl.
auto 9.
**
apply DI2.
apply DE'.
rewrite ?eq_subst.
cbn.
subsimpl.
apply IE with (z ∈' s).
eapply CE1 with (z ≡' x ∨ z ≡' x ~> z ∈' s).
replace (z ∈' s <~> z ≡' x ∨ z ≡' x) with (($0 ∈' s`[↑] <~> $0 ≡' x`[↑] ∨ $0 ≡' x`[↑])[z..]).
2: cbn; rewrite ?eq_subst; cbn; now subsimpl.
apply AllE.
auto 7.
eapply minZF_elem; auto 9.
2: apply (Weak H2); auto.
apply minZF_refl.
auto 9.
+
apply (ExI o).
cbn.
subsimpl.
rewrite !is_om_subst.
cbn.
Admitted.

Lemma prv_to_min_om2 { p : peirce } : binZF ⊢ rm_const_fm ax_om2.
Proof.
cbn.
prv_all' x.
destruct x as [n|[]].
cbn.
rewrite rm_const_fm_subst, inductive_subst, !is_inductive_subst.
cbn.
apply II.
prv_all' m.
cbn.
rewrite !is_inductive_subst.
cbn.
simpl_ex.
rewrite !is_inductive_subst.
cbn.
apply II.
simpl_ex.
change (∃ $0 ≡' ↑ n ∧ m`[↑] ∈' $0) with (∃ $0 ≡' $n`[↑] ∧ m`[↑] ∈' $0).
simpl_ex.
assert1 H.
use_exists' H k.
clear H.
cbn.
rewrite !is_inductive_subst.
cbn.
subsimpl.
assert1 H.
apply CE in H as [H1 % CE2 H2].
apply (AllE $n) in H1.
cbn in H1.
subsimpl_in H1.
rewrite is_inductive_subst in H1.
cbn in H1.
assert3 H3.
apply prv_to_min_inductive in H3; auto.
apply (IE H1) in H3.
apply (AllE m) in H3.
cbn in H3.
subsimpl_in H3.
Admitted.

Lemma prv_to_min { p : peirce } phi : phi el ZFeq' -> binZF ⊢ rm_const_fm phi.
Proof.
intros [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]].
-
apply prv_to_min_refl.
-
apply prv_to_min_sym.
-
apply prv_to_min_trans.
-
apply prv_to_min_elem.
-
apply prv_to_min_ext.
-
apply prv_to_min_eset.
-
apply prv_to_min_pair.
-
apply prv_to_min_union.
-
apply prv_to_min_power.
-
apply prv_to_min_om1.
-
Admitted.

Lemma rm_const_tm_prv { p : peirce } t : binZF ⊢ ∃ rm_const_tm t.
Proof.
induction t; try destruct F; cbn.
-
apply (ExI $x).
cbn.
apply minZF_refl'.
-
apply Ctx.
firstorder.
-
rewrite (vec_inv2 v).
cbn.
assert (H1 : binZF ⊢ ∃ rm_const_tm (Vector.hd v)) by apply IH, in_hd.
assert (H2 : binZF ⊢ ∃ rm_const_tm (Vector.hd (Vector.tl v))) by apply IH, in_hd_tl.
use_exists' H1 x.
eapply Weak in H2.
use_exists' H2 y.
2: auto.
assert (H : binZF ⊢ ax_pair') by (apply Ctx; firstorder).
apply (AllE x) in H.
cbn in H.
apply (AllE y) in H.
cbn in H.
eapply Weak in H.
use_exists' H z.
2: auto.
apply (ExI z).
cbn.
apply (ExI x).
cbn.
subsimpl.
rewrite eq_sshift1.
apply CI; auto.
apply (ExI y).
cbn.
subsimpl.
erewrite !subst_comp, subst_ext.
rewrite eq_subst.
cbn.
subsimpl.
apply CI; auto.
now intros [].
-
rewrite (vec_inv1 v).
cbn.
specialize (IH _ (in_hd v)).
use_exists' IH x.
assert (H : binZF ⊢ ax_union') by (apply Ctx; firstorder).
apply (AllE x) in H.
cbn in H.
eapply Weak in H.
use_exists' H y.
2: auto.
apply (ExI y).
cbn.
apply (ExI x).
cbn.
subsimpl.
rewrite eq_sshift1.
apply CI; auto.
-
rewrite (vec_inv1 v).
cbn.
specialize (IH _ (in_hd v)).
use_exists' IH x.
assert (H : binZF ⊢ ax_power') by (apply Ctx; firstorder).
apply (AllE x) in H.
cbn in H.
eapply Weak in H.
use_exists' H y.
2: auto.
apply (ExI y).
cbn.
apply (ExI x).
cbn.
subsimpl.
rewrite eq_sshift1.
apply CI; auto.
-
apply Ctx.
Admitted.

Lemma rm_const_tm_sub { p : peirce } A t (x y : term') : binZF <<= A -> A ⊢ (rm_const_tm t)[x..] -> A ⊢ (rm_const_tm t)[y..] -> A ⊢ sub' x y.
Proof.
intros HA.
induction t in A, HA, x, y |- *; try destruct F; cbn -[is_inductive sub'].
-
intros H1 H2.
prv_all' z.
apply II.
eapply minZF_elem; auto; try apply minZF_refl; auto.
eapply minZF_trans; auto.
apply (Weak H1); auto.
apply minZF_sym; auto.
apply (Weak H2).
auto.
-
intros H _.
prv_all' z.
apply II.
apply Exp.
apply (AllE z) in H.
cbn in H.
subsimpl_in H.
eapply IE; try apply (Weak H); auto.
-
rewrite (vec_inv2 v).
cbn.
rewrite !eq_sshift1.
intros H1 H2.
prv_all' a.
apply II.
eapply Weak in H1.
use_exists' H1 b.
2: auto.
clear H1.
assert1 H.
apply CE in H as [H1 H3].
eapply Weak in H3.
use_exists' H3 c.
2: auto.
clear H3.
assert1 H.
apply CE in H as [H3 H4].
eapply Weak in H2.
use_exists' H2 d.
2: auto.
clear H2.
assert1 H.
apply CE in H as [H2 H5].
eapply Weak in H5.
use_exists' H5 e.
2: auto.
clear H5.
assert1 H.
apply CE in H as [H5 H6].
pose (B := ((rm_const_tm (Vector.hd v))[b..] ∧ (∃ (rm_const_tm (Vector.hd (Vector.tl v)))[sshift 2][up (up x..)][up b..] ∧ (∀ $0 ∈' x`[↑]`[↑] <~> $0 ≡' b`[↑]`[↑] ∨ $0 ≡' ↑ 0)) :: a ∈' x :: A)).
fold B in H1, H2, H3, H4, H5, H6.
fold B.
rewrite !eq_sshift2, !eq_sshift1 in *.
assert (HB : binZF <<= B).
{
rewrite HA.
unfold B.
auto.
}
apply (AllE a) in H6.
cbn in H6.
subsimpl_in H6.
eapply IE.
eapply CE2.
apply H6.
apply (AllE a) in H4.
cbn in H4.
subsimpl_in H4.
eapply DE.
+
eapply IE.
eapply CE1.
apply (Weak H4); auto.
apply Ctx.
unfold B.
auto.
+
apply DI1.
rewrite ?eq_subst.
cbn.
subsimpl.
eapply minZF_trans; auto.
apply minZF_ext; auto.
*
eapply (IH _ (in_hd v)); auto; eapply Weak.
apply H1.
auto.
apply H2.
auto.
*
eapply (IH _ (in_hd v)); auto; eapply Weak.
apply H2.
auto.
apply H1.
auto.
+
apply DI2.
rewrite ?eq_subst.
cbn.
subsimpl.
eapply minZF_trans; auto.
apply minZF_ext; auto.
*
eapply (IH _ (in_hd_tl v)); auto; eapply Weak.
apply H3.
auto.
apply H5.
auto.
*
eapply (IH _ (in_hd_tl v)); auto; eapply Weak.
apply H5.
auto.
apply H3.
auto.
-
rewrite (vec_inv1 v).
cbn.
rewrite !eq_sshift1 in *.
intros H1 H2.
prv_all' a.
apply II.
eapply Weak in H1.
use_exists' H1 b.
2: auto.
eapply Weak in H2.
use_exists' H2 c.
2: auto.
clear H1 H2.
assert1 H.
apply CE in H as [H1 H2].
apply (AllE a) in H2.
cbn in H2.
subsimpl_in H2.
eapply IE.
eapply CE2, H2.
clear H2.
assert2 H.
apply CE in H as [H2 H3].
apply (AllE a) in H3.
cbn in H3.
subsimpl_in H3.
apply CE1 in H3.
assert3 H4.
apply (IE H3) in H4.
use_exists' H4 d.
clear H3 H4.
apply (ExI d).
cbn.
subsimpl.
apply CI.
2: eapply CE2; auto.
eapply (IH _ (in_hd v) _ b c) in H1; auto.
apply (AllE d) in H1.
cbn in H1.
subsimpl_in H1.
eapply Weak in H1.
apply (IE H1).
2: auto.
eapply CE1; auto.
-
rewrite (vec_inv1 v).
cbn.
rewrite !eq_sshift1.
intros H1 H2.
prv_all' a.
apply II.
eapply Weak in H1.
use_exists' H1 b.
2: auto.
eapply Weak in H2.
use_exists' H2 c.
2: auto.
clear H1 H2.
assert1 H.
apply CE in H as [H1 H2].
apply (AllE a) in H2.
cbn in H2.
subsimpl_in H2.
eapply IE.
eapply CE2, H2.
clear H2.
assert2 H.
apply CE in H as [H2 H3].
apply (AllE a) in H3.
cbn in H3.
subsimpl_in H3.
apply CE1 in H3.
assert3 H4.
apply (IE H3) in H4.
clear H3.
prv_all' d.
apply II.
apply (IH _ (in_hd v) _ b c) in H1; auto.
apply (AllE d) in H1.
cbn in H1.
subsimpl_in H1.
eapply Weak in H1.
apply (IE H1).
2: auto.
apply (AllE d) in H4.
cbn in H4.
subsimpl_in H4.
eapply Weak in H4.
apply (IE H4).
all: auto.
-
intros [H1 H2] % CE [H3 H4] % CE.
apply (AllE y) in H2.
cbn -[is_inductive] in H2.
subsimpl_in H2.
apply (IE H2).
Admitted.

Lemma rm_const_tm_equiv { p : peirce } A t (x y : term') : binZF <<= A -> A ⊢ (rm_const_tm t)[x..] -> A ⊢ y ≡' x <-> A ⊢ (rm_const_tm t)[y..].
Proof.
intros HA Hx.
split; intros H.
-
eapply minZF_Leibniz; eauto.
-
Admitted.

Lemma inductive_subst t sigma : (inductive t)[sigma] = inductive t`[sigma].
Proof.
cbn.
subsimpl.
reflexivity.
