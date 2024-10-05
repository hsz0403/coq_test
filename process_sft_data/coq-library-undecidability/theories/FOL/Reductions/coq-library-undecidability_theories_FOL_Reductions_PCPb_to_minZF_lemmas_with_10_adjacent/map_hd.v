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

Lemma vec_nil_eq X (v : vec X 0) : v = Vector.nil.
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

Instance min_model : interp sig_empty _ V.
Proof.
split.
-
intros [].
-
Admitted.

Lemma min_embed_eval (rho : nat -> V) (t : term') : eval rho (embed_t t) = eval rho t.
Proof.
destruct t as [|[]].
Admitted.

Lemma min_embed (rho : nat -> V) (phi : form') : sat I rho (embed phi) <-> sat min_model rho phi.
Proof.
induction phi in rho |- *; try destruct b0; try destruct q; cbn.
1,3-7: firstorder.
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

Lemma map_hd X Y n (f : X -> Y) (v : vec X (S n)) : Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
depelim v.
reflexivity.
