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

Lemma or_equiv { p : peirce } (phi psi phi' psi' : form') A : (forall B, A <<= B -> B ⊢ phi <-> B ⊢ phi') -> (forall B, A <<= B -> B ⊢ psi <-> B ⊢ psi') -> (A ⊢ phi ∨ psi) <-> (A ⊢ phi' ∨ psi').
Proof.
intros H1 H2.
split; intros H; apply (DE H).
1,3: apply DI1; apply H1; auto.
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
apply H1; auto.
