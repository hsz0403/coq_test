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

Lemma map_hd X Y n (f : X -> Y) (v : vec X (S n)) : Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
depelim v.
Admitted.

Lemma map_tl X Y n (f : X -> Y) (v : vec X (S n)) : Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
Proof.
depelim v.
Admitted.

Lemma in_hd X n (v : vec X (S n)) : Vector.In (Vector.hd v) v.
Proof.
depelim v.
Admitted.

Lemma in_hd_tl X n (v : vec X (S (S n))) : Vector.In (Vector.hd (Vector.tl v)) v.
Proof.
depelim v.
constructor.
depelim v.
Admitted.

Lemma vec_inv1 X (v : vec X 1) : v = Vector.cons (Vector.hd v) Vector.nil.
Proof.
repeat depelim v.
cbn.
Admitted.

Lemma vec_inv2 X (v : vec X 2) : v = Vector.cons (Vector.hd v) (Vector.cons (Vector.hd (Vector.tl v)) Vector.nil).
Proof.
repeat depelim v.
cbn.
Admitted.

Instance min_model : interp sig_empty sig_binary V.
Proof.
split.
-
intros [].
-
intros [] v.
Admitted.

Lemma min_embed_eval (rho : nat -> V) (t : term') : eval rho (embed_t t) = eval rho t.
Proof.
destruct t as [|[]].
Admitted.

Lemma min_embed (rho : nat -> V) (phi : form') : sat I rho (embed phi) <-> sat min_model rho phi.
Proof.
induction phi in rho |- *; try destruct b0; try destruct q; cbn.
1,3-7: firstorder.
destruct P.
erewrite Vector.map_map, Vector.map_ext.
reflexivity.
Admitted.

Lemma embed_subst_t (sigma : nat -> term') (t : term') : embed_t t`[sigma] = (embed_t t)`[sigma >> embed_t].
Proof.
induction t; cbn; trivial.
Admitted.

Lemma embed_subst (sigma : nat -> term') (phi : form') : embed phi[sigma] = (embed phi)[sigma >> embed_t].
Proof.
induction phi in sigma |- *; cbn; trivial.
-
f_equal.
erewrite !Vector.map_map, Vector.map_ext.
reflexivity.
apply embed_subst_t.
-
firstorder congruence.
-
rewrite IHphi.
f_equal.
apply subst_ext.
intros []; cbn; trivial.
unfold funcomp.
cbn.
unfold funcomp.
Admitted.

Lemma embed_sshift n (phi : form') : embed phi[sshift n] = (embed phi)[sshift n].
Proof.
rewrite embed_subst.
apply subst_ext.
Admitted.

Lemma sat_sshift1 (rho : nat -> V) x y (phi : form) : (y .: x .: rho) ⊨ phi[sshift 1] <-> (y .: rho) ⊨ phi.
Proof.
erewrite sat_comp, sat_ext.
reflexivity.
Admitted.

Lemma sat_sshift2 (rho : nat -> V) x y z (phi : form) : (z .: y .: x .: rho) ⊨ phi[sshift 2] <-> (z .: rho) ⊨ phi.
Proof.
erewrite sat_comp, sat_ext.
reflexivity.
Admitted.

Lemma eq_equiv x y : x ≈ y <-> x ≡ y.
Proof.
split.
-
intros H.
apply sing_el; trivial.
apply H.
apply sing_el; trivial.
now apply set_equiv_equiv.
-
intros H z.
apply set_equiv_elem; trivial.
Admitted.

Lemma inductive_sat (rho : nat -> V) x : (x .: rho) ⊨ is_inductive $0 -> M_inductive x.
Proof.
cbn.
setoid_rewrite eq_equiv.
split.
-
destruct H as [[y Hy] _].
enough (H : ∅ ≡ y).
{
eapply set_equiv_elem; eauto.
now apply set_equiv_equiv.
apply Hy.
}
apply M_ext; trivial; intros z Hz; exfalso; intuition.
now apply M_eset in Hz.
-
intros y [z Hz] % H.
enough (Hx : σ y ≡ z).
{
eapply set_equiv_elem; eauto.
now apply set_equiv_equiv.
apply Hz.
}
apply M_ext; trivial.
+
intros a Ha % sigma_el; trivial.
now apply Hz.
+
intros a Ha % Hz.
Admitted.

Lemma M_om1 : M_inductive ω.
Proof.
apply (@M_ZF (fun _ => ∅) ax_om1).
Admitted.

Lemma inductive_sat_om (rho : nat -> V) : (ω .: rho) ⊨ is_inductive $0.
Proof.
cbn.
setoid_rewrite eq_equiv.
split.
-
exists ∅.
split; try apply M_eset; trivial.
now apply M_om1.
-
intros d Hd.
exists (σ d).
split; try now apply M_om1.
intros d'.
Admitted.

Instance set_equiv_equiv' : Equivalence set_equiv.
Proof.
Admitted.

Instance set_equiv_elem' : Proper (set_equiv ==> set_equiv ==> iff) set_elem.
Proof.
Admitted.

Lemma vec_nil_eq X (v : vec X 0) : v = Vector.nil.
Proof.
depelim v.
reflexivity.
