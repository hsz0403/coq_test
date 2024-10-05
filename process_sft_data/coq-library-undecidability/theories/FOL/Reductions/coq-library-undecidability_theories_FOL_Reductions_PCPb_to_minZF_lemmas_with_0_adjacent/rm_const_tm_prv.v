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

Lemma rm_const_tm_prv { p : peirce } t : minZFeq' ⊢ ∃ rm_const_tm t.
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
assert (H1 : minZFeq' ⊢ ∃ rm_const_tm (Vector.hd v)) by apply IH, in_hd.
assert (H2 : minZFeq' ⊢ ∃ rm_const_tm (Vector.hd (Vector.tl v))) by apply IH, in_hd_tl.
use_exists' H1 x.
eapply Weak in H2.
use_exists' H2 y.
2: auto.
assert (H : minZFeq' ⊢ ax_pair') by (apply Ctx; firstorder).
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
apply CI; auto.
now intros [].
-
rewrite (vec_inv1 v).
cbn.
specialize (IH _ (in_hd v)).
use_exists' IH x.
assert (H : minZFeq' ⊢ ax_union') by (apply Ctx; firstorder).
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
assert (H : minZFeq' ⊢ ax_power') by (apply Ctx; firstorder).
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
firstorder.
