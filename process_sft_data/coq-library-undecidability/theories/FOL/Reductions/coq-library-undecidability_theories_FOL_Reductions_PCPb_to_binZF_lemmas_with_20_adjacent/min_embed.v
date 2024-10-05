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

Lemma vec_nil_eq X (v : vec X 0) : v = Vector.nil.
Proof.
depelim v.
Admitted.

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

Instance set_equiv_sub' : Proper (set_equiv ==> set_equiv ==> iff) set_sub.
Proof.
Admitted.

Instance equiv_union' : Proper (set_equiv ==> set_equiv) union.
Proof.
Admitted.

Instance equiv_power' : Proper (set_equiv ==> set_equiv) power.
Proof.
Admitted.

Lemma rm_const_tm_sat (rho : nat -> V) (t : term) x : (x .: rho) ⊨ embed (rm_const_tm t) <-> set_equiv x (eval rho t).
Proof.
induction t in x |- *; try destruct F; cbn; split; try rewrite (vec_inv1 v); try rewrite (vec_inv2 v); cbn.
-
now apply eq_equiv.
-
now apply eq_equiv.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
intros H.
apply M_ext; trivial; intros y Hy; exfalso; intuition.
now apply M_eset in Hy.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
change (set_equiv x ∅ -> forall d : V, set_elem d x -> False).
intros H d.
rewrite H.
now apply M_eset.
-
intros (y & Hy & z & Hz & H).
rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
rewrite embed_sshift, sat_sshift2, IH in Hz; try apply in_hd_tl.
apply M_ext; trivial.
+
intros a Ha % H.
rewrite !eq_equiv in Ha.
apply M_pair; trivial.
rewrite <- Hy, <- Hz.
tauto.
+
intros a Ha % M_pair; trivial.
apply H.
rewrite !eq_equiv.
rewrite <- Hy, <- Hz in Ha.
tauto.
-
exists (eval rho (Vector.hd v)).
rewrite embed_sshift, sat_sshift1, IH; try apply in_hd.
split; try reflexivity.
exists (eval rho (Vector.hd (Vector.tl v))).
rewrite embed_sshift, sat_sshift2, IH; try apply in_hd_tl.
split; try reflexivity.
change (forall d, (set_elem d x -> d ≈ eval rho (Vector.hd v) \/ d ≈ eval rho (Vector.hd (Vector.tl v))) /\ (d ≈ eval rho (Vector.hd v) \/ d ≈ eval rho (Vector.hd (Vector.tl v)) -> set_elem d x)).
intros d.
rewrite !eq_equiv, H.
now apply M_pair.
-
intros (y & Hy & H).
rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
change (set_equiv x (union (eval rho (Vector.hd v)))).
rewrite <- Hy.
apply M_ext; trivial.
+
intros z Hz % H.
now apply M_union.
+
intros z Hz % M_union; trivial.
now apply H.
-
exists (eval rho (Vector.hd v)).
rewrite embed_sshift, sat_sshift1, IH; try apply in_hd.
split; try reflexivity.
change (forall d, (set_elem d x -> exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) /\ ((exists d0 : V, d0 ∈ eval rho (Vector.hd v) /\ d ∈ d0) -> set_elem d x)).
intros d.
rewrite H.
now apply M_union.
-
intros (y & Hy & H).
rewrite embed_sshift, sat_sshift1, IH in Hy; try apply in_hd.
change (set_equiv x (power (eval rho (Vector.hd v)))).
rewrite <- Hy.
apply M_ext; trivial.
+
intros z Hz.
apply M_power; trivial.
unfold set_sub.
now apply H.
+
intros z Hz.
now apply H, M_power.
-
exists (eval rho (Vector.hd v)).
rewrite embed_sshift, sat_sshift1, IH; try apply in_hd.
split; try reflexivity.
change (forall d, (set_elem d x -> d ⊆ eval rho (Vector.hd v)) /\ (d ⊆ eval rho (Vector.hd v) -> set_elem d x)).
intros d.
rewrite H.
now apply M_power.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
intros [H1 H2].
apply M_ext; trivial.
+
unfold set_sub.
apply H2.
apply (inductive_sat_om rho).
+
unfold set_sub.
apply M_om2; trivial.
apply inductive_sat with rho.
apply H1.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
split.
+
change ((exists d : V, (forall d0 : V, d0 ∈ d -> False) /\ set_elem d x) /\ (forall d : V, set_elem d x -> exists d0 : V, (forall d1 : V, (d1 ∈ d0 -> d1 ∈ d \/ d1 ≈ d) /\ (d1 ∈ d \/ d1 ≈ d -> d1 ∈ d0)) /\ set_elem d0 x)).
setoid_rewrite H.
apply (inductive_sat_om rho).
+
intros d Hd.
change (set_sub x d).
rewrite H.
unfold set_sub.
apply M_om2; trivial.
apply inductive_sat with rho.
Admitted.

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
rewrite eq_equiv.
split; trivial.
reflexivity.
+
intros (x & Hx & y & Hy & H).
apply rm_const_tm_sat in Hx.
change (set_equiv (eval rho (Vector.hd t)) (eval rho (Vector.hd (Vector.tl t)))).
rewrite embed_sshift, sat_sshift1, rm_const_tm_sat in Hy.
rewrite <- Hx, <- Hy.
now apply eq_equiv.
-
split; intros; intuition.
-
Admitted.

Theorem min_correct (rho : nat -> V) (phi : form) : sat I rho phi <-> sat min_model rho (rm_const_fm phi).
Proof.
rewrite <- min_embed.
Admitted.

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

Lemma min_embed (rho : nat -> V) (phi : form') : sat I rho (embed phi) <-> sat min_model rho phi.
Proof.
induction phi in rho |- *; try destruct b0; try destruct q; cbn.
1,3-7: firstorder.
destruct P.
erewrite Vector.map_map, Vector.map_ext.
reflexivity.
apply min_embed_eval.
