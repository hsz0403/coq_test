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

Lemma min_axioms' (rho : nat -> V) : rho ⊫ binZF.
Proof.
intros A [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn.
-
intros x y H1 H2.
apply eq_equiv.
now apply M_ext.
-
intros x y u v H1 % eq_equiv H2 % eq_equiv.
now apply set_equiv_elem'.
-
exists ∅.
apply (@M_ZF rho ax_eset).
firstorder.
-
intros x y.
exists ({x; y}).
setoid_rewrite eq_equiv.
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
rewrite !eq_equiv.
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
all: intros y; rewrite sigma_el; trivial.
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

Lemma eq_subst x y sigma : (x ≡' y)[sigma] = (x`[sigma] ≡' y`[sigma]).
Proof.
unfold eq'.
cbn.
subsimpl.
Admitted.

Lemma minZF_refl' { p : peirce } t : binZF ⊢ t ≡' t.
Proof.
prv_all' x.
Admitted.

Lemma minZF_sym { p : peirce } A x y : binZF <<= A -> A ⊢ x ≡' y -> A ⊢ y ≡' x.
Proof.
intros HA H.
prv_all' z.
apply (AllE z) in H.
cbn in H.
subsimpl_in H.
apply CE in H.
Admitted.

Lemma minZF_trans { p : peirce } A x y z : binZF <<= A -> A ⊢ x ≡' y -> A ⊢ y ≡' z -> A ⊢ x ≡' z.
Proof.
intros HA H1 H2.
prv_all' a.
apply (AllE a) in H1.
cbn in H1.
subsimpl_in H1.
apply (AllE a) in H2.
cbn in H2.
subsimpl_in H2.
apply CE in H1 as [H1 H1'].
apply CE in H2 as [H2 H2'].
apply CI; apply II; eapply IE.
-
apply (Weak H2); auto.
-
now apply imps.
-
apply (Weak H1'); auto.
-
Admitted.

Lemma minZF_elem' { p : peirce } x y u v : binZF ⊢ x ≡' u ~> y ≡' v ~> x ∈' y ~> u ∈' v.
Proof.
assert (binZF ⊢ ax_eq_elem').
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
rewrite !eq_subst in H.
cbn in H.
subsimpl_in H.
Admitted.

Lemma minZF_elem { p : peirce } A x y u v : binZF <<= A -> A ⊢ x ≡' u -> A ⊢ y ≡' v -> A ⊢ x ∈' y -> A ⊢ u ∈' v.
Proof.
intros HA H1 H2 H3.
eapply IE.
eapply IE.
eapply IE.
eapply Weak.
eapply minZF_elem'.
auto.
Admitted.

Lemma minZF_ext { p : peirce } A x y : binZF <<= A -> A ⊢ sub' x y -> A ⊢ sub' y x -> A ⊢ x ≡' y.
Proof.
intros HA H1 H2.
assert (HS : A ⊢ ax_ext').
apply Ctx.
firstorder.
apply (AllE x) in HS.
unfold eq' in HS.
cbn in HS.
apply (AllE y) in HS.
cbn in HS.
subsimpl_in HS.
eapply IE.
now apply (IE HS).
Admitted.

Lemma minZF_Leibniz_tm { p : peirce } A (t : term') x y : binZF <<= A -> A ⊢ x ≡' y -> A ⊢ t`[x..] ≡' t`[y..].
Proof.
intros HA H.
destruct t as [[]|[]]; cbn; trivial.
Admitted.

Lemma and_equiv { p : peirce } (phi psi phi' psi' : form') A : (A ⊢ phi <-> A ⊢ phi') -> (A ⊢ psi <-> A ⊢ psi') -> (A ⊢ phi ∧ psi) <-> (A ⊢ phi' ∧ psi').
Proof.
intros H1 H2.
Admitted.

Lemma or_equiv { p : peirce } (phi psi phi' psi' : form') A : (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi ∨ psi) <-> (A ⊢ phi' ∨ psi').
Proof.
intros H1 H2.
split; intros H; apply (DE H).
1,3: apply DI1; apply H1; auto.
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

Lemma minZF_refl { p : peirce } A t : binZF <<= A -> A ⊢ t ≡' t.
Proof.
apply Weak, minZF_refl'.
