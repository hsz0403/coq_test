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

Lemma rm_const_tm_sat (rho : nat -> V) (t : term) x : (x .: rho) ⊨ rm_const_tm t <-> x = eval rho t.
Proof.
induction t in x |- *; try destruct F; cbn; split; try intros ->; try rewrite (vec_inv1 v); try rewrite (vec_inv2 v); cbn.
-
now rewrite VIEQ.
-
now rewrite VIEQ.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
intros H.
apply M_ext; trivial; intros y Hy; exfalso; intuition.
now apply M_eset in Hy.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
intros d.
now apply M_eset.
-
intros (y & Hy & z & Hz & H).
rewrite sat_sshift1, IH in Hy; try apply in_hd.
subst.
rewrite sat_sshift2, IH in Hz; try apply in_hd_tl.
subst.
apply M_ext; trivial.
+
intros a Ha % H.
rewrite !VIEQ in Ha.
now apply M_pair.
+
intros a Ha % M_pair; trivial.
apply H.
now rewrite !VIEQ.
-
exists (eval rho (Vector.hd v)).
rewrite sat_sshift1, IH; try apply in_hd.
split; trivial.
exists (eval rho (Vector.hd (Vector.tl v))).
rewrite sat_sshift2, IH; try apply in_hd_tl.
split; trivial.
intros d.
rewrite !VIEQ.
now apply M_pair.
-
intros (y & Hy & H).
rewrite sat_sshift1, IH in Hy; try apply in_hd.
subst.
apply M_ext; trivial.
+
intros y Hy % H.
now apply M_union.
+
intros y Hy % M_union; trivial.
now apply H.
-
exists (eval rho (Vector.hd v)).
rewrite sat_sshift1, IH; try apply in_hd.
split; trivial.
intros d.
now apply M_union.
-
intros (y & Hy & H).
rewrite sat_sshift1, IH in Hy; try apply in_hd.
subst.
apply M_ext; trivial.
+
intros y Hy.
now apply M_power, H.
+
intros y Hy.
now apply H, M_power.
-
exists (eval rho (Vector.hd v)).
rewrite sat_sshift1, IH; try apply in_hd.
split; trivial.
intros d.
now apply M_power.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
intros [H1 H2].
apply M_ext; trivial.
+
apply H2.
apply (inductive_sat_om rho).
+
apply M_om2; trivial.
apply inductive_sat with rho.
apply H1.
-
rewrite (vec_nil_eq (Vector.map (eval rho) v)).
split.
+
apply (inductive_sat_om rho).
+
intros d Hd.
apply M_om2; trivial.
apply inductive_sat with rho.
apply Hd.
