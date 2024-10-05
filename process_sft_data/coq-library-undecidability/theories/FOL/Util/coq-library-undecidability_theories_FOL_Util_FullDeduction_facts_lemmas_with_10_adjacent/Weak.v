From Undecidability Require Import FOL.Util.FullTarski_facts FOL.Util.Syntax_facts.
From Undecidability Require Import Shared.ListAutomation.
From Undecidability Require Export FOL.Util.FullDeduction.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Require Import Lia.
Ltac comp := repeat (progress (cbn in *; autounfold in *)).
Section ND_def.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ff : falsity_flag}.
Context {p : peirce}.
Hint Constructors prv : core.
Definition cycle_shift n x := if Dec (n = x) then $0 else $(S x).
End ND_def.
Hint Constructors prv : core.
Section Soundness.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
End Soundness.
Ltac subsimpl_in H := rewrite ?up_term, ?subst_term_shift in H.
Ltac subsimpl := rewrite ?up_term, ?subst_term_shift.
Ltac assert1 H := match goal with |- (?phi :: ?T) ⊢ _ => assert (H : (phi :: T) ⊢ phi) by auto end.
Ltac assert2 H := match goal with |- (?phi :: ?psi :: ?T) ⊢ _ => assert (H : (phi :: psi :: T) ⊢ psi) by auto end.
Ltac assert3 H := match goal with |- (?phi :: ?psi :: ?theta :: ?T) ⊢ _ => assert (H : (phi :: psi :: theta :: T) ⊢ theta) by auto end.
Ltac assert4 H := match goal with |- (?f :: ?phi :: ?psi :: ?theta :: ?T) ⊢ _ => assert (H : (f :: phi :: psi :: theta :: T) ⊢ theta) by auto end.
Ltac prv_all x := apply AllI; edestruct nameless_equiv_all as [x ->]; cbn; subsimpl.
Ltac use_exists H x := apply (ExE _ H); edestruct nameless_equiv_ex as [x ->]; cbn; subsimpl.

Theorem subst_Weak A phi xi : A ⊢ phi -> [phi[xi] | phi ∈ A] ⊢ phi[xi].
Proof.
induction 1 in xi |-*; comp.
1-2,7-15: eauto using in_map.
-
apply AllI.
setoid_rewrite map_map in IHprv.
erewrite map_map, map_ext.
apply IHprv.
intros ?.
cbn.
now rewrite up_form.
-
specialize (IHprv xi).
apply AllE with (t0 := t`[xi]) in IHprv.
rewrite subst_comp in *.
erewrite subst_ext; try apply IHprv.
intros [|]; cbn; trivial.
unfold funcomp.
now setoid_rewrite subst_term_shift.
-
specialize (IHprv xi).
eapply ExI with (t0 := t`[xi]).
rewrite subst_comp in *.
erewrite subst_ext; try apply IHprv.
intros [|]; cbn; trivial.
unfold funcomp.
now setoid_rewrite subst_term_shift.
-
eapply ExE in IHprv1.
eassumption.
rewrite map_map.
specialize (IHprv2 (up xi)).
setoid_rewrite up_form in IHprv2.
erewrite map_map, map_ext in IHprv2; try apply IHprv2.
Admitted.

Lemma cycle_shift_shift n phi : bounded n phi -> phi[cycle_shift n] = phi[↑].
Proof.
intros H.
apply (bounded_subst H).
intros k.
unfold cycle_shift.
Admitted.

Lemma cycle_shift_subject n phi : bounded (S n) phi -> phi[$n..][cycle_shift n] = phi.
Proof.
intros H.
erewrite subst_comp, (bounded_subst H), subst_id; trivial.
Admitted.

Lemma nameless_equiv_all' A phi n : bounded_L n A -> bounded (S n) phi -> [p[↑] | p ∈ A] ⊢ phi <-> A ⊢ phi[$n..].
Proof.
intros H1 H2.
split; intros H.
-
apply (subst_Weak ($n..)) in H.
rewrite map_map in *.
erewrite map_ext, map_id in H; try apply H.
intros.
apply subst_shift.
-
apply (subst_Weak (cycle_shift n)) in H.
rewrite (map_ext_in _ (subst_form ↑)) in H.
+
now rewrite cycle_shift_subject in H.
+
intros psi HP.
Admitted.

Lemma nameless_equiv_ex' A phi psi n : bounded_L n A -> bounded n phi -> bounded (S n) psi -> (psi::[p0[↑] | p0 ∈ A]) ⊢ phi[↑] <-> (psi[$n..]::A) ⊢ phi.
Proof.
intros HL Hphi Hpsi.
split.
-
intros H % (subst_Weak ($n..)).
cbn in *.
rewrite map_map, (map_ext _ id), map_id in H.
+
now rewrite subst_shift in H.
+
intros.
apply subst_shift.
-
intros H % (subst_Weak (cycle_shift n)).
cbn in *.
rewrite (map_ext_in _ (subst_form ↑)) in H.
+
now rewrite cycle_shift_subject, cycle_shift_shift in H.
+
intros theta HT.
Admitted.

Lemma nameless_equiv_all A phi : { t : term | map (subst_form ↑) A ⊢ phi <-> A ⊢ phi[t..] }.
Proof.
destruct (find_bounded_L (phi::A)) as [n H].
exists $n.
apply nameless_equiv_all'.
-
intros ? ?.
apply H.
auto.
-
Admitted.

Lemma nameless_equiv_ex A phi psi : { t : term | (phi :: map (subst_form ↑) A) ⊢ psi[↑] <-> (phi[t..]::A) ⊢ psi }.
Proof.
destruct (find_bounded_L (phi::psi::A)) as [n H].
exists $n.
apply nameless_equiv_ex'.
-
intros ? ?.
apply H.
auto.
-
apply H.
auto.
-
Admitted.

Lemma imps T phi psi : T ⊢ phi ~> psi <-> (phi :: T) ⊢ psi.
Proof.
split; try apply II.
intros H.
apply IE with phi; auto.
apply (Weak H).
Admitted.

Lemma CE T phi psi : T ⊢ phi ∧ psi -> T ⊢ phi /\ T ⊢ psi.
Proof.
intros H.
split.
-
apply (CE1 H).
-
Admitted.

Lemma DE' A phi : A ⊢ phi ∨ phi -> A ⊢ phi.
Proof.
intros H.
Admitted.

Theorem Weak A B phi : A ⊢ phi -> A <<= B -> B ⊢ phi.
Proof.
intros H.
revert B.
induction H; intros B HB; try unshelve (solve [econstructor; intuition]); try now econstructor.
