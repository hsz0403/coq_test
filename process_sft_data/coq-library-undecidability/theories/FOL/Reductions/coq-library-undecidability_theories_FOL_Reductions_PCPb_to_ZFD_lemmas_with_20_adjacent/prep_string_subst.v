Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction_facts.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Reductions.PCPb_to_ZF.
From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Local Definition BSRS := list(card bool).
Local Notation "x / y" := (x, y).
Section ZF.
Context { p : peirce }.
Close Scope sem.
Fixpoint tnumeral n := match n with | O => ∅ | S n => σ (tnumeral n) end.
Definition sing x := {x; x}.
Fixpoint enc_derivations B n := match n with | O => sing (opair ∅ (enc_stack B)) | S n => enc_derivations B n ∪ sing (opair (tnumeral (S n)) (enc_stack (derivations B (S n)))) end.
Local Arguments comb_rel : simpl never.
Local Arguments is_rep : simpl never.
End ZF.

Lemma ZF_bunion_inv T x y z : ZFeq' <<= T -> T ⊢ z ∈ x ∪ y -> T ⊢ z ∈ x ∨ z ∈ y.
Proof.
intros HT H.
eapply IE; try apply H.
eapply Weak; try apply HT.
Admitted.

Lemma ZF_eq_bunion T x y x' y' : ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ x ∪ y ≡ x' ∪ y'.
Proof.
intros HT H1 H2.
Admitted.

Lemma ZF_sig_el T x : ZFeq' <<= T -> T ⊢ x ∈ σ x.
Proof.
intros H.
apply ZF_bunion_el'; trivial.
apply DI2.
apply ZF_sing_iff; trivial.
apply ZF_refl'.
Admitted.

Lemma ZF_eq_sig T x y : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ σ x ≡ σ y.
Proof.
intros HT H.
Admitted.

Lemma sing_pair1 T x y z : ZFeq' <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ y.
Proof.
intros HT H.
apply ZF_sym'; trivial.
apply ZF_sing_iff; trivial.
eapply ZF_eq_elem; trivial.
apply ZF_refl'; trivial.
apply ZF_sym'; eauto.
apply ZF_pair_el'; trivial.
apply DI1.
Admitted.

Lemma sing_pair2 T x y z : ZFeq' <<= T -> T ⊢ sing x ≡ {y; z} -> T ⊢ x ≡ z.
Proof.
intros HT H.
apply ZF_sym'; trivial.
apply ZF_sing_iff; trivial.
eapply ZF_eq_elem; trivial.
apply ZF_refl'; trivial.
apply ZF_sym'; eauto.
apply ZF_pair_el'; trivial.
apply DI2.
Admitted.

Lemma opair_inj1 T x y x' y' : ZFeq' <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ x ≡ x'.
Proof.
intros HT He.
assert (H : T ⊢ {x; x} ∈ opair x y).
{
apply ZF_pair_el'; trivial.
apply DI1.
now apply ZF_refl'.
}
eapply ZF_eq_elem in H; try apply He; try apply ZF_refl'; trivial.
apply ZF_pair_el' in H; trivial.
Admitted.

Lemma opair_inj2 T x y x' y' : ZFeq' <<= T -> T ⊢ opair x y ≡ opair x' y' -> T ⊢ y ≡ y'.
Proof.
intros HT H.
assert (H' : T ⊢ y ≡ x' ∨ y ≡ y').
-
assert (H2 : T ⊢ {x; y} ∈ opair x' y').
{
eapply ZF_eq_elem; trivial.
apply ZF_refl'; trivial.
apply H.
apply ZF_pair_el'; trivial.
apply DI2.
now apply ZF_refl'.
}
apply ZF_pair_el' in H2; trivial.
apply (DE H2).
+
apply DI1.
apply ZF_sym'; auto.
eapply sing_pair2; auto.
apply ZF_sym'; auto.
+
apply ZF_pair_el'; auto.
eapply ZF_eq_elem; auto.
*
apply ZF_refl'; auto.
*
apply ZF_pair_el'; auto.
apply DI2.
apply ZF_refl'.
auto.
-
apply (DE H'); try apply prv_T1.
assert (H1 : T ⊢ x ≡ x') by apply (opair_inj1 HT H).
assert (H2 : T ⊢ {x'; y'} ∈ opair x y).
{
eapply ZF_eq_elem; trivial.
apply ZF_refl'; trivial.
apply ZF_sym', H; trivial.
apply ZF_pair_el'; trivial.
apply DI2.
now apply ZF_refl'.
}
apply ZF_pair_el' in H2; trivial.
eapply DE; try eapply (Weak H2); auto.
+
eapply ZF_trans'; auto.
eapply ZF_trans'; auto.
*
apply ZF_sym'.
auto.
apply (Weak H1).
auto.
*
eapply sing_pair2; auto.
apply ZF_sym'; auto.
+
eapply ZF_trans'; auto.
eapply sing_pair2; auto.
eapply ZF_trans'; auto.
2: apply ZF_sym'; auto.
eapply ZF_eq_pair; try apply ZF_sym'; auto.
apply (Weak H1).
auto.
+
Admitted.

Lemma ZF_bunion_el1 T x y z : ZFeq' <<= T -> T ⊢ z ∈ x -> T ⊢ z ∈ x ∪ y.
Proof.
intros HT H.
Admitted.

Lemma ZF_bunion_el2 T x y z : ZFeq' <<= T -> T ⊢ z ∈ y -> T ⊢ z ∈ x ∪ y.
Proof.
intros HT H.
Admitted.

Lemma bunion_eset x : ZFeq' ⊢ ∅ ∪ x ≡ x.
Proof.
apply ZF_ext'; auto; prv_all y; apply II.
-
eapply DE.
eapply ZF_bunion_inv; auto.
+
apply Exp.
eapply IE.
eapply Weak; try apply ZF_eset.
all: auto.
+
auto.
-
Admitted.

Lemma bunion_swap x y z : ZFeq' ⊢ (x ∪ y) ∪ z ≡ (x ∪ z) ∪ y.
Proof.
apply ZF_ext'; auto; prv_all u; apply II.
-
eapply DE.
eapply ZF_bunion_inv; auto.
+
eapply DE.
eapply ZF_bunion_inv; auto.
*
apply ZF_bunion_el1, ZF_bunion_el1.
all: auto.
*
apply ZF_bunion_el2; auto.
+
apply ZF_bunion_el1, ZF_bunion_el2.
all: auto.
-
eapply DE.
eapply ZF_bunion_inv; auto.
+
eapply DE.
eapply ZF_bunion_inv; auto.
*
apply ZF_bunion_el1, ZF_bunion_el1.
all: auto.
*
apply ZF_bunion_el2; auto.
+
apply ZF_bunion_el1, ZF_bunion_el2.
Admitted.

Lemma bunion_use T x y z phi : ZFeq' <<= T -> (x ∈ y :: T) ⊢ phi -> (x ≡ z :: T) ⊢ phi -> T ⊢ x ∈ y ∪ sing z ~> phi.
Proof.
intros HT H1 H2.
apply II.
eapply DE.
-
eapply ZF_bunion_inv; auto.
-
apply (Weak H1).
auto.
-
eapply IE.
+
eapply Weak.
apply II, H2.
auto.
+
Admitted.

Lemma ZF_numeral_trans T n x y : ZFeq' <<= T -> T ⊢ x ∈ tnumeral n ~> y ∈ x ~> y ∈ tnumeral n.
Proof.
intros HT.
induction n; cbn.
-
apply II, Exp.
eapply IE.
apply ZF_eset'.
all: auto.
-
apply bunion_use; trivial.
+
rewrite !imps.
rewrite !imps in IHn.
apply ZF_bunion_el1; auto.
+
apply II.
apply ZF_bunion_el'.
auto.
apply DI1.
eapply ZF_eq_elem; auto.
apply ZF_refl'.
Admitted.

Lemma ZF_numeral_wf T n : ZFeq' <<= T -> T ⊢ ¬ (tnumeral n ∈ tnumeral n).
Proof.
intros HT.
induction n; cbn.
-
now apply ZF_eset'.
-
apply bunion_use; trivial.
+
eapply IE.
apply (Weak IHn).
auto.
eapply IE.
eapply IE.
apply ZF_numeral_trans; auto.
auto.
apply ZF_sig_el.
auto.
+
eapply IE.
apply (Weak IHn).
auto.
eapply ZF_eq_elem.
auto.
apply ZF_refl'.
auto.
auto.
apply ZF_sig_el.
Admitted.

Lemma enc_derivations_base R n : ZFeq' ⊢ {{∅; ∅}; {∅; enc_stack R}} ∈ enc_derivations R n.
Proof.
induction n; cbn.
-
apply ZF_sing_el.
-
apply ZF_bunion_el.
Admitted.

Lemma enc_derivations_step B n : ZFeq' ⊢ opair (tnumeral n) (enc_stack (derivations B n)) ∈ enc_derivations B n.
Proof.
destruct n; cbn.
-
apply ZF_sing_el.
-
apply ZF_bunion_el.
apply DI2.
Admitted.

Lemma enc_stack_spec R s t : s/t el R -> ZFeq' ⊢ opair (enc_string s) (enc_string t) ∈ enc_stack R.
Proof.
induction R as [|[u v] R IH]; cbn; auto.
intros [[=]| H]; subst.
-
apply ZF_bunion_el.
apply DI2.
apply ZF_sing_el.
-
apply ZF_bunion_el.
apply DI1.
Admitted.

Lemma ZF_derivations_bound T B k n x : ZFeq' <<= T -> T ⊢ opair k x ∈ enc_derivations B n -> T ⊢ k ∈ σ (tnumeral n).
Proof.
induction n in T |- *; cbn; intros HT H.
-
apply ZF_sing_iff in H; trivial.
eapply ZF_eq_elem; trivial.
apply ZF_sym'; trivial.
eapply opair_inj1; trivial.
apply H.
apply ZF_refl'; trivial.
eapply ZF_bunion_el'; trivial.
apply DI2.
apply ZF_sing_iff; trivial.
apply ZF_refl'; trivial.
-
apply ZF_bunion_inv in H; trivial.
apply (DE H).
+
apply ZF_bunion_el1.
auto.
apply IHn; auto.
+
apply ZF_bunion_el2.
auto.
apply ZF_sing_iff.
auto.
eapply opair_inj1.
auto.
Admitted.

Lemma enc_derivations_functional B n x y y' : ZFeq' ⊢ opair x y ∈ enc_derivations B n ~> opair x y' ∈ enc_derivations B n ~> y ≡ y'.
Proof.
induction n; cbn -[derivations].
-
repeat apply II.
eapply opair_inj2.
auto.
eapply ZF_trans'.
auto.
+
apply ZF_sing_iff; auto.
+
apply ZF_sym'.
auto.
apply ZF_sing_iff; auto.
-
apply bunion_use; try apply bunion_use.
1,2,5: auto.
+
repeat rewrite <- imps.
now apply (Weak IHn).
+
apply Exp.
eapply IE.
apply (@ZF_numeral_wf _ (S n)).
auto.
eapply ZF_derivations_bound.
auto.
eapply ZF_eq_elem.
auto.
2: apply ZF_refl'; auto.
2: auto.
apply ZF_eq_opair; auto.
eapply opair_inj1; auto.
apply ZF_refl'.
auto.
+
apply Exp.
eapply IE.
apply (@ZF_numeral_wf _ (S n)).
auto.
eapply ZF_derivations_bound.
auto.
eapply ZF_eq_elem.
auto.
2: apply ZF_refl'; auto.
2: auto.
apply ZF_eq_opair; auto.
eapply opair_inj1; auto.
apply ZF_refl'.
auto.
+
eapply opair_inj2.
auto.
eapply ZF_trans'; auto.
Admitted.

Lemma enc_stack_subst sigma B : (enc_stack B)`[sigma] = enc_stack B.
Proof.
induction B as [|[s t] B IH]; cbn; trivial.
rewrite IH.
unfold enc_string.
Admitted.

Lemma is_rep_subst s t x y sigma : (is_rep (comb_rel s t) x y)[sigma] = is_rep (comb_rel s t) x`[sigma] y`[sigma].
Proof.
unfold is_rep.
cbn -[comb_rel].
subsimpl.
repeat f_equal.
-
unfold comb_rel.
cbn.
rewrite !prep_string_subst.
reflexivity.
-
unfold comb_rel.
cbn.
rewrite !prep_string_subst.
Admitted.

Lemma combinations_subst B x y sigma : (combinations B x y)[sigma] = combinations B x`[sigma] y`[sigma].
Proof.
induction B as [|[s t] B IH] in sigma, x, y |- *.
-
cbn.
reflexivity.
-
cbn -[is_rep].
rewrite IH, is_rep_subst.
cbn -[is_rep].
Admitted.

Lemma enc_derivations_eq T B n x : ZFeq' <<= T -> T ⊢ opair (tnumeral n) x ∈ enc_derivations B n -> T ⊢ x ≡ enc_stack (derivations B n).
Proof.
intros HT H.
destruct n; cbn in *.
-
eapply opair_inj2; trivial.
eapply ZF_sing_iff; eauto.
-
apply ZF_bunion_inv in H; trivial.
apply (DE H).
+
apply Exp.
eapply IE.
apply (ZF_numeral_wf (S n)).
auto.
eapply ZF_derivations_bound.
auto.
auto.
+
eapply opair_inj2.
auto.
apply ZF_sing_iff.
auto.
Admitted.

Lemma enc_stack_app T B C : ZFeq' <<= T -> T ⊢ (enc_stack B) ∪ (enc_stack C) ≡ enc_stack (B ++ C).
Proof.
intros HT.
induction B as [|[s t] B IH]; cbn.
-
eapply Weak; try apply bunion_eset.
assumption.
-
eapply ZF_trans'; trivial.
eapply Weak; try apply bunion_swap; trivial.
eapply ZF_eq_bunion; trivial.
Admitted.

Lemma prep_string_app s t x : prep_string (s ++ t) x = prep_string s (prep_string t x).
Proof.
Admitted.

Lemma ZF_eq_prep T s x y : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ prep_string s x ≡ prep_string s y.
Proof.
intros HT H.
induction s; cbn; try tauto.
apply ZF_eq_opair; trivial.
Admitted.

Lemma append_all_el T B s t x y : ZFeq' <<= T -> T ⊢ opair x y ∈ enc_stack B -> T ⊢ opair (prep_string s x) (prep_string t y) ∈ enc_stack (append_all B (s/t)).
Proof.
intros HT H.
induction B as [|[u v] B IH] in T, HT, H |- *; cbn in *.
-
apply Exp.
eapply IE.
2: apply H.
now apply ZF_eset'.
-
eapply (ZF_bunion_el' HT).
eapply DE.
apply (ZF_bunion_inv HT H).
+
apply DI1.
apply IH; auto.
+
assert1 H'.
apply ZF_sing_iff in H'; try now auto.
apply DI2.
apply ZF_sing_iff.
auto.
rewrite !prep_string_app.
apply ZF_eq_opair.
auto.
*
apply ZF_eq_prep.
auto.
eapply opair_inj1; eauto.
*
apply ZF_eq_prep.
auto.
Admitted.

Lemma is_rep_eq T B s t x y : ZFeq' <<= T -> T ⊢ x ≡ enc_stack B -> T ⊢ is_rep (comb_rel s t) x y -> T ⊢ y ≡ enc_stack (append_all B (s / t)).
Proof.
intros HT H1 H2.
apply ZF_ext'; trivial.
-
prv_all a.
apply (AllE a) in H2.
cbn in H2.
subsimpl_in H2.
eapply CE1 in H2.
rewrite imps in *.
use_exists H2 z.
assert1 H.
apply CE in H as [H H'].
unfold comb_rel at 2 in H'.
cbn in H'.
subsimpl_in H'.
rewrite !prep_string_subst in H'.
cbn in H'.
use_exists H' c.
clear H'.
cbn.
subsimpl.
rewrite !prep_string_subst.
cbn.
assert1 H'.
use_exists H' d.
clear H'.
cbn.
subsimpl.
rewrite !prep_string_subst.
cbn.
subsimpl.
eapply ZF_eq_elem.
auto.
apply ZF_sym'.
auto.
eapply CE2.
auto.
apply ZF_refl'.
auto.
apply append_all_el.
auto.
eapply ZF_eq_elem.
auto.
eapply CE1.
auto.
eapply (Weak H1).
auto.
eapply (Weak H).
auto.
-
prv_all a.
apply (AllE a) in H2.
cbn in H2.
subsimpl_in H2.
eapply CE2 in H2.
apply II.
eapply IE; try apply (Weak H2).
auto.
induction B as [|[u v] B IH] in T, x, HT, H1 |- *; cbn in *.
+
apply Exp.
eapply IE.
apply ZF_eset'.
all: auto.
+
rewrite <- imps.
apply bunion_use; trivial.
*
specialize (IH T (enc_stack B) HT).
assert (H : T ⊢ enc_stack B ≡ enc_stack B) by now apply ZF_refl'.
apply IH in H.
use_exists H z.
clear H.
apply ExI with z.
cbn.
subsimpl.
assert1 H.
apply CE in H as [H H'].
apply CI; trivial.
eapply ZF_eq_elem.
auto.
apply ZF_refl'.
auto.
apply ZF_sym'.
auto.
apply (Weak H1).
auto.
apply ZF_bunion_el1; trivial.
auto.
*
apply ExI with (opair (enc_string u) (enc_string v)).
cbn.
subsimpl.
apply CI.
--
eapply ZF_eq_elem.
auto.
apply ZF_refl'.
auto.
apply ZF_sym'.
auto.
apply (Weak H1).
auto.
apply ZF_bunion_el2.
auto.
eapply Weak.
apply ZF_sing_el.
auto.
--
cbn.
apply ExI with (enc_string v).
cbn.
apply ExI with (enc_string u).
cbn.
subsimpl.
rewrite !prep_string_subst, !prep_string_app; cbn.
subsimpl.
apply CI; auto.
apply ZF_refl'.
Admitted.

Lemma combinations_eq T B C x y : ZFeq' <<= T -> T ⊢ x ≡ enc_stack C -> T ⊢ combinations B x y -> T ⊢ y ≡ enc_stack (derivation_step B C).
Proof.
induction B as [|[s t] B IH] in y, T |-*; cbn; intros HT H1 H2; trivial.
use_exists H2 u.
assert1 H.
use_exists H v.
clear H.
rewrite !combinations_subst, !is_rep_subst.
cbn.
subsimpl.
eapply ZF_trans'.
auto.
eapply CE1.
eapply CE1.
auto.
eapply ZF_trans'.
auto.
2: apply enc_stack_app; auto.
apply ZF_eq_bunion; auto.
-
eapply is_rep_eq; auto.
apply (Weak H1); auto.
eapply CE2.
auto.
-
apply IH; auto.
+
apply (Weak H1); auto.
+
eapply CE2.
eapply CE1.
Admitted.

Lemma combinations_step B n (i x y : term) : ZFeq' ⊢ i ∈ tnumeral n ~> opair i x ∈ enc_derivations B n ~> combinations B x y ~> opair (σ i) y ∈ enc_derivations B n.
Proof.
induction n; cbn.
-
apply II.
apply Exp.
apply imps.
apply ZF_eset.
-
apply bunion_use; try apply bunion_use; auto.
+
apply II.
apply ZF_bunion_el'.
auto.
apply DI1.
eapply IE.
eapply IE.
eapply IE.
*
eapply Weak.
apply IHn.
auto.
*
auto.
*
auto.
*
auto.
+
apply Exp.
eapply IE.
apply (ZF_numeral_wf (S n)).
auto.
eapply ZF_eq_elem.
auto.
eapply opair_inj1.
auto.
auto.
apply ZF_refl'.
auto.
cbn.
apply ZF_bunion_el'.
auto.
apply DI1.
auto.
+
apply II.
apply ZF_bunion_el'.
auto.
apply DI2.
apply ZF_sing_iff.
auto.
apply ZF_eq_opair.
auto.
*
apply ZF_eq_sig; auto.
*
eapply combinations_eq; auto.
apply enc_derivations_eq.
auto.
eapply ZF_eq_elem; auto; try apply ZF_refl'; auto.
eapply ZF_eq_opair; auto; try apply ZF_refl'.
auto.
+
apply Exp.
eapply IE.
apply (ZF_numeral_wf n).
auto.
eapply ZF_eq_elem.
auto.
apply ZF_refl'.
auto.
eapply ZF_trans'.
auto.
apply ZF_sym'.
auto.
eapply opair_inj1.
auto.
auto.
auto.
apply ZF_sig_el.
Admitted.

Theorem dPCP_ZFD B : dPCPb B -> ZFeq' ⊢ solvable B.
Proof.
intros [s H].
destruct (derivable_derivations H) as [n Hn].
unfold solvable.
apply ExI with (tnumeral n).
cbn.
apply ExI with (enc_derivations B n).
cbn.
apply ExI with (enc_string s).
cbn.
subsimpl.
apply ExI with (enc_stack (derivations B n)).
cbn.
rewrite !enc_stack_subst, !combinations_subst.
cbn.
subsimpl.
repeat apply CI.
-
apply ZF_numeral.
-
prv_all x.
prv_all y.
prv_all z.
apply enc_derivations_functional.
-
apply enc_derivations_base.
-
prv_all x.
prv_all y.
prv_all z.
rewrite !combinations_subst.
cbn.
subsimpl.
apply combinations_step.
-
apply enc_derivations_step.
-
Admitted.

Theorem PCP_ZFD B : PCPb B -> ZFeq' ⊢ solvable B.
Proof.
rewrite PCPb_iff_dPCPb.
Admitted.

Lemma prep_string_subst sigma s x : (prep_string s x)`[sigma] = prep_string s x`[sigma].
Proof.
induction s; cbn; trivial.
rewrite IHs.
destruct a; reflexivity.
