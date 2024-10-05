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

Lemma min_axioms' (rho : nat -> V) : rho ⊫ minZF'.
Proof.
intros A [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn.
-
apply (@M_ZF rho ax_ext).
firstorder.
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
rewrite !VIEQ.
now apply sigma_el.
+
intros x [H1 H2].
apply (@M_ZF rho ax_om2); cbn.
auto 8.
split.
*
destruct H1 as (e & E1 & E2).
enough (∅ = e) as -> by assumption.
apply M_ext; trivial.
all: intros y Hy; exfalso; try now apply E1 in Hy.
apply (@M_ZF rho ax_eset) in Hy; trivial.
unfold ZF'.
auto 8.
*
intros d (s & S1 & S2) % H2.
enough (σ d = s) as -> by assumption.
apply M_ext; trivial.
all: intros y; rewrite sigma_el; trivial.
Admitted.

Lemma min_axioms : (forall rho phi, ZF phi -> rho ⊨ phi) -> forall rho phi, minZF phi -> rho ⊨ phi.
Proof.
intros H rho phi [].
-
now apply min_axioms'.
-
cbn.
specialize (H rho (ax_sep (embed phi0))).
cbn in H.
setoid_rewrite (subst_ext _ _ (($0 .: (fun m : nat => S (S (S m))) >> var) >> embed_t)) in H; try now intros [].
rewrite <- embed_subst in H.
setoid_rewrite min_embed in H.
apply H.
auto using ZF.
-
cbn.
specialize (H rho (ax_rep (embed phi0))).
cbn in H.
setoid_rewrite (subst_ext _ _ (($2 .: $1 .: Nat.add 3 >> var) >> embed_t)) in H at 1; try now intros [|[]].
setoid_rewrite (subst_ext _ _ (($2 .: $0 .: Nat.add 3 >> var) >> embed_t)) in H at 2; try now intros [|[]].
setoid_rewrite (subst_ext _ _ (($0 .: $1 .: Nat.add 4 >> var) >> embed_t)) in H at 3; try now intros [|[]].
setoid_rewrite (subst_ext _ _ (($0 .: $1 .: Nat.add 4 >> var) >> embed_t)) in H at 4; try now intros [|[]].
rewrite <- !embed_subst in H.
setoid_rewrite min_embed in H.
apply H.
Admitted.

Lemma extensional_eq_min' V (M : @interp sig_empty _ V) rho : extensional M -> rho ⊫ minZF' -> rho ⊫ minZFeq'.
Proof.
intros H1 H2 phi [<-|[<-|[<-|[<-|H]]]]; try now apply H2.
Admitted.

Lemma extensional_eq_min V (M : @interp sig_empty _ V) rho : extensional M -> (forall phi, minZF phi -> rho ⊨ phi) -> (forall phi, minZFeq phi -> rho ⊨ phi).
Proof.
intros H1 H2 phi []; try now apply H2; auto using minZF.
Admitted.

Lemma up_sshift1 (phi : form') sigma : phi[sshift 1][up (up sigma)] = phi[up sigma][sshift 1].
Proof.
rewrite !subst_comp.
apply subst_ext.
intros []; trivial.
cbn.
unfold funcomp.
Admitted.

Lemma up_sshift2 (phi : form') sigma : phi[sshift 2][up (up (up sigma))] = phi[up sigma][sshift 2].
Proof.
rewrite !subst_comp.
apply subst_ext.
intros [|[]]; trivial.
cbn.
unfold funcomp.
now destruct (sigma 0) as [|[]].
cbn.
unfold funcomp.
Admitted.

Lemma rm_const_tm_subst (sigma : nat -> term') (t : term) : (rm_const_tm t)[up sigma] = rm_const_tm t`[sigma >> embed_t].
Proof.
induction t; cbn; try destruct F.
-
unfold funcomp.
now destruct (sigma x) as [k|[]].
-
reflexivity.
-
cbn.
rewrite (vec_inv2 v).
cbn.
rewrite up_sshift2, up_sshift1, !IH; trivial.
apply in_hd_tl.
apply in_hd.
-
cbn.
rewrite (vec_inv1 v).
cbn.
rewrite up_sshift1, IH; trivial.
apply in_hd.
-
cbn.
rewrite (vec_inv1 v).
cbn.
rewrite up_sshift1, IH; trivial.
apply in_hd.
-
Admitted.

Lemma rm_const_fm_subst (sigma : nat -> term') (phi : form) : (rm_const_fm phi)[sigma] = rm_const_fm phi[sigma >> embed_t].
Proof.
induction phi in sigma |- *; cbn; trivial; try destruct P.
-
rewrite (vec_inv2 t).
cbn.
now rewrite up_sshift1, !rm_const_tm_subst.
-
rewrite (vec_inv2 t).
cbn.
now rewrite up_sshift1, !rm_const_tm_subst.
-
firstorder congruence.
-
rewrite IHphi.
f_equal.
erewrite subst_ext.
reflexivity.
intros []; trivial.
unfold funcomp.
cbn.
unfold funcomp.
Admitted.

Lemma rm_const_fm_shift (phi : form) : (rm_const_fm phi)[↑] = rm_const_fm phi[↑].
Proof.
rewrite rm_const_fm_subst.
erewrite subst_ext.
reflexivity.
Admitted.

Lemma eq_sshift1 (phi : form') t : phi[sshift 1][up t..] = phi.
Proof.
erewrite subst_comp, subst_id; try reflexivity.
Admitted.

Lemma eq_sshift2 (phi : form') t : phi[sshift 2][up (up t..)] = phi[sshift 1].
Proof.
erewrite subst_comp, subst_ext; try reflexivity.
Admitted.

Lemma minZF_refl' { p : peirce } t : minZFeq' ⊢ t ≡' t.
Proof.
change (minZFeq' ⊢ ($0 ≡' $0)[t..]).
apply AllE.
apply Ctx.
Admitted.

Lemma minZF_refl { p : peirce } A t : minZFeq' <<= A -> A ⊢ t ≡' t.
Proof.
Admitted.

Lemma minZF_sym { p : peirce } A x y : minZFeq' <<= A -> A ⊢ x ≡' y -> A ⊢ y ≡' x.
Proof.
intros HA H.
assert (HS : A ⊢ ax_sym').
apply Ctx.
firstorder.
apply (AllE x) in HS.
cbn in HS.
apply (AllE y) in HS.
cbn in HS.
subsimpl_in HS.
Admitted.

Lemma minZF_trans { p : peirce } A x y z : minZFeq' <<= A -> A ⊢ x ≡' y -> A ⊢ y ≡' z -> A ⊢ x ≡' z.
Proof.
intros HA H1 H2.
assert (HS : A ⊢ ax_trans').
apply Ctx.
firstorder.
apply (AllE x) in HS.
cbn in HS.
apply (AllE y) in HS.
cbn in HS.
apply (AllE z) in HS.
cbn in HS.
subsimpl_in HS.
eapply IE.
now apply (IE HS).
Admitted.

Lemma minZF_elem' { p : peirce } x y u v : minZFeq' ⊢ x ≡' u ~> y ≡' v ~> x ∈' y ~> u ∈' v.
Proof.
assert (minZFeq' ⊢ ax_eq_elem').
apply Ctx.
firstorder.
apply (AllE x) in H.
cbn in H.
apply (AllE y) in H.
cbn in H.
apply (AllE u) in H.
cbn in H.
apply (AllE v) in H.
cbn in H.
subsimpl_in H.
Admitted.

Lemma minZF_elem { p : peirce } A x y u v : minZFeq' <<= A -> A ⊢ x ≡' u -> A ⊢ y ≡' v -> A ⊢ x ∈' y -> A ⊢ u ∈' v.
Proof.
intros HA H1 H2 H3.
eapply IE.
eapply IE.
eapply IE.
eapply Weak.
eapply minZF_elem'.
auto.
Admitted.

Lemma minZF_ext { p : peirce } A x y : minZFeq' <<= A -> A ⊢ sub' x y -> A ⊢ sub' y x -> A ⊢ x ≡' y.
Proof.
intros HA H1 H2.
assert (HS : A ⊢ ax_ext').
apply Ctx.
firstorder.
apply (AllE x) in HS.
cbn in HS.
apply (AllE y) in HS.
cbn in HS.
subsimpl_in HS.
eapply IE.
now apply (IE HS).
Admitted.

Lemma minZF_Leibniz_tm { p : peirce } A (t : term') x y : minZFeq' <<= A -> A ⊢ x ≡' y -> A ⊢ t`[x..] ≡' t`[y..].
Proof.
intros HA H.
destruct t as [[]|[]]; cbn; trivial.
Admitted.

Lemma and_equiv { p : peirce } (phi psi phi' psi' : form') A : (A ⊢ phi <-> A ⊢ phi') -> (A ⊢ psi <-> A ⊢ psi') -> (A ⊢ phi ∧ psi) <-> (A ⊢ phi' ∧ psi').
Proof.
intros H1 H2.
Admitted.

Lemma impl_equiv { p : peirce } (phi psi phi' psi' : form') A : (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi ~> psi) <-> (A ⊢ phi' ~> psi').
Proof.
intros H1 H2.
split; intros H; apply II.
-
apply H2; auto.
eapply IE.
apply (Weak H).
auto.
apply H1; auto.
-
apply H2; auto.
eapply IE.
apply (Weak H).
auto.
Admitted.

Lemma all_equiv { p : peirce } (phi psi : form') A : (forall t, A ⊢ phi[t..] <-> A ⊢ psi[t..]) -> (A ⊢ ∀ phi) <-> (A ⊢ ∀ psi).
Proof.
intros H1.
split; intros H2; apply AllI.
Admitted.

Lemma ex_equiv { p : peirce } (phi psi : form') A : (forall B t, A <<= B -> B ⊢ phi[t..] <-> B ⊢ psi[t..]) -> (A ⊢ ∃ phi) <-> (A ⊢ ∃ psi).
Proof.
intros H1.
split; intros H2.
-
apply (ExE _ H2).
edestruct (nameless_equiv_ex A) as [x ->].
apply ExI with x.
apply H1; auto.
-
apply (ExE _ H2).
edestruct (nameless_equiv_ex A) as [x ->].
apply ExI with x.
Admitted.

Lemma minZF_Leibniz { p : peirce } A (phi : form') x y : minZFeq' <<= A -> A ⊢ x ≡' y -> A ⊢ phi[x..] <-> A ⊢ phi[y..].
Proof.
revert A.
induction phi using form_ind_subst; cbn; intros A HA HXY; try tauto.
-
destruct P0; rewrite (vec_inv2 t); cbn; split.
+
apply minZF_elem; trivial; now apply minZF_Leibniz_tm.
+
apply minZF_sym in HXY; trivial.
apply minZF_elem; trivial; now apply minZF_Leibniz_tm.
+
intros H.
eapply minZF_trans; trivial.
apply minZF_Leibniz_tm; trivial.
eapply minZF_sym; eauto.
eapply minZF_trans; trivial.
apply H.
now apply minZF_Leibniz_tm.
+
intros H.
eapply minZF_trans; trivial.
apply minZF_Leibniz_tm; eauto.
eapply minZF_trans; trivial.
apply H.
apply minZF_Leibniz_tm; trivial.
now apply minZF_sym.
-
destruct b0.
+
apply and_equiv; intuition.
+
apply or_equiv; intros B HB.
*
apply IHphi1.
now rewrite HA.
now apply (Weak HXY).
*
apply IHphi2.
now rewrite HA.
now apply (Weak HXY).
+
apply impl_equiv; intros B HB.
*
apply IHphi1.
now rewrite HA.
now apply (Weak HXY).
*
apply IHphi2.
now rewrite HA.
now apply (Weak HXY).
-
destruct x as [n|[]], y as [m|[]].
destruct q.
+
apply all_equiv.
intros [k|[]].
specialize (H ($(S k)..) A HA HXY).
erewrite !subst_comp, subst_ext, <- subst_comp.
rewrite H.
erewrite !subst_comp, subst_ext.
reflexivity.
all: now intros [|[]]; cbn.
+
apply ex_equiv.
intros B [k|[]] HB.
cbn.
specialize (H ($(S k)..) B).
erewrite !subst_comp, subst_ext, <- subst_comp.
rewrite H.
2: now rewrite HA.
2: now apply (Weak HXY).
erewrite !subst_comp, subst_ext.
reflexivity.
Admitted.

Lemma iff_equiv { p : peirce } (phi psi phi' psi' : form') A : (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi <~> psi) <-> (A ⊢ phi' <~> psi').
Proof.
intros H1 H2.
split; intros [H3 H4] % CE; apply CI; eapply impl_equiv.
3,9: apply H3.
5,10: apply H4.
Admitted.

Lemma prv_ex_eq { p : peirce } A x phi : minZFeq' <<= A -> A ⊢ phi[x..] <-> A ⊢ ∃ $0 ≡' x`[↑] ∧ phi.
Proof.
intros HA.
split; intros H.
-
apply (ExI x).
cbn.
subsimpl.
apply CI; trivial.
now apply minZF_refl.
-
use_exists' H y.
eapply minZF_Leibniz; eauto 3.
Admitted.

Lemma use_ex_eq { p : peirce } A x phi psi : minZFeq' <<= A -> A ⊢ phi[x..] ~> psi <-> A ⊢ (∃ $0 ≡' x`[↑] ∧ phi) ~> psi.
Proof.
intros H.
apply impl_equiv; try tauto.
intros B HB.
apply prv_ex_eq.
Admitted.

Lemma prv_to_min_refl { p : peirce } : minZFeq' ⊢ rm_const_fm ax_refl.
Proof.
prv_all' x.
repeat simpl_ex.
Admitted.

Lemma prv_to_min_sym { p : peirce } : minZFeq' ⊢ rm_const_fm ax_sym.
Proof.
prv_all' x.
prv_all' y.
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

Lemma prv_to_min_trans { p : peirce } : minZFeq' ⊢ rm_const_fm ax_trans.
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

Lemma prv_to_min_elem { p : peirce } : minZFeq' ⊢ rm_const_fm ax_eq_elem.
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

Lemma prv_to_min_ext { p : peirce } : minZFeq' ⊢ rm_const_fm ax_ext.
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

Lemma prv_to_min_eset { p : peirce } : minZFeq' ⊢ rm_const_fm ax_eset.
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

Lemma prv_to_min_pair { p : peirce } : minZFeq' ⊢ rm_const_fm ax_pair.
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
assert (HP : minZFeq' ⊢ ax_pair') by (apply Ctx; firstorder).
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
*
apply DI2.
assert1 H.
Admitted.

Lemma prv_to_min_union { p : peirce } : minZFeq' ⊢ rm_const_fm ax_union.
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
assert (HU : minZFeq' ⊢ ax_union') by (apply Ctx; firstorder).
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
simpl_ex.
apply Ctx.
auto.
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

Lemma prv_to_min_power { p : peirce } : minZFeq' ⊢ rm_const_fm ax_power.
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
assert (HP : minZFeq' ⊢ ax_power') by (apply Ctx; firstorder).
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

Lemma prv_to_min_inductive { p : peirce } A n : minZFeq' <<= A -> A ⊢ rm_const_fm (inductive $n) -> A ⊢ is_inductive $n.
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
2: auto.
apply minZF_refl.
rewrite <- HB, HA.
auto 8.
--
apply DI2.
apply (AllE b) in H.
cbn in H.
subsimpl_in H.
apply CE1 in H.
eapply DE'.
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

Lemma inductive_subst t sigma : (inductive t)[sigma] = inductive t`[sigma].
Proof.
cbn.
subsimpl.
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

Lemma or_equiv { p : peirce } (phi psi phi' psi' : form') A : (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi ∨ psi) <-> (A ⊢ phi' ∨ psi').
Proof.
intros H1 H2.
split; intros H; apply (DE H).
1,3: apply DI1; apply H1; auto.
1,2: apply DI2; apply H2; auto.
