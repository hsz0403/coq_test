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

Theorem min_correct (rho : nat -> V) (phi : form) : sat I rho phi <-> sat min_model rho (rm_const_fm phi).
Proof.
Admitted.

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

Lemma eq_sshift1 (phi : form') t : phi[sshift 1][up t..] = phi.
Proof.
erewrite subst_comp, subst_id; try reflexivity.
now intros [].
