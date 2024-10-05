From Undecidability.FOL Require Import Util.FullTarski_facts Util.Syntax_facts Util.FullDeduction_facts.
From Undecidability.FOL Require Import ZF Reductions.PCPb_to_ZF minZF.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Require Import Equations.Equations.
Local Notation vec := Vector.t.
Definition embed_t (t : term') : term := match t with | $x => $x | func f ts => False_rect term f end.
Fixpoint embed {ff'} (phi : form sig_empty ZF_pred_sig _ ff') : form ff' := match phi with | atom P ts => atom P (Vector.map embed_t ts) | bin b phi psi => bin b (embed phi) (embed psi) | quant q phi => quant q (embed phi) | ⊥ => ⊥ end.
Definition sshift {Σ_funcs : funcs_signature} k : nat -> term := fun n => match n with 0 => $0 | S n => $(1 + k + n) end.
Fixpoint rm_const_tm (t : term) : form' := match t with | var n => $0 ≡' var (S n) | func eset _ => is_eset $0 | func pair v => let v' := Vector.map rm_const_tm v in ∃ (Vector.hd v')[sshift 1] ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 2] ∧ is_pair $1 $0 $2 | func union v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_union $0 $1 | func power v => ∃ (Vector.hd (Vector.map rm_const_tm v))[sshift 1] ∧ is_power $0 $1 | func omega v => is_om $0 end.
Fixpoint rm_const_fm {ff : falsity_flag} (phi : form) : form' := match phi with | ⊥ => ⊥ | bin bop phi psi => bin sig_empty _ bop (rm_const_fm phi) (rm_const_fm psi) | quant qop phi => quant qop (rm_const_fm phi) | atom elem v => let v' := Vector.map rm_const_tm v in ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ∈'$0 | atom equal v => let v' := Vector.map rm_const_tm v in ∃ (Vector.hd v') ∧ ∃ (Vector.hd (Vector.tl v'))[sshift 1] ∧ $1 ≡' $0 end.
Derive Signature for vec.
Section Model.
Open Scope sem.
Context {V : Type} {I : interp V}.
Hypothesis M_ZF : forall rho, rho ⊫ ZF'.
Hypothesis VIEQ : extensional I.
Instance min_model : interp sig_empty _ V.
Proof.
split.
-
intros [].
-
now apply i_atom.
Defined.
End Model.
Ltac prv_all' x := apply AllI; edestruct (@nameless_equiv_all sig_empty) as [x ->]; cbn; subsimpl.
Ltac use_exists' H x := apply (ExE _ H); edestruct (@nameless_equiv_ex sig_empty) as [x ->]; cbn; subsimpl.
Local Ltac simpl_ex := try apply prv_ex_eq; try apply use_ex_eq; auto; cbn; subsimpl.
Local Ltac simpl_ex_in H := try apply prv_ex_eq in H; try apply use_ex_eq in H; auto; cbn in H; subsimpl_in H.
Local Arguments is_om : simpl never.
Local Arguments is_inductive : simpl never.
Local Arguments inductive : simpl never.
Local Arguments is_om : simpl nomatch.
Section Deduction.
End Deduction.

Lemma rm_const_tm_sub { p : peirce } A t (x y : term') : minZFeq' <<= A -> A ⊢ (rm_const_tm t)[x..] -> A ⊢ (rm_const_tm t)[y..] -> A ⊢ sub' x y.
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
assert (HB : minZFeq' <<= B).
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
apply H3.
