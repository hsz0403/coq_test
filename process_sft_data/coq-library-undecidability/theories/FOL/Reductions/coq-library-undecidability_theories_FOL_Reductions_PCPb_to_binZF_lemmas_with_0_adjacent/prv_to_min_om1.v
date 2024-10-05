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
apply CI; [eapply CE1 | eapply CE2]; auto.
