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

Lemma ZF_pair_el x y z : ZFeq' ⊢ (z ≡ x ∨ z ≡ y) -> ZFeq' ⊢ z ∈ {x; y}.
Proof.
Admitted.

Lemma ZF_sub_pair T x y x' y' : ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ⊆ {x'; y'}.
Proof.
intros HT H1 H2.
prv_all z.
apply II.
apply ZF_pair_el'; auto.
eapply DE.
-
apply ZF_pair_el'; auto.
-
apply DI1.
eapply ZF_trans'; auto.
eapply Weak; eauto.
-
apply DI2.
eapply ZF_trans'; auto.
Admitted.

Lemma ZF_eq_pair T x y x' y' : ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ {x; y} ≡ {x'; y'}.
Proof.
intros HT H1 H2.
apply ZF_ext'; trivial.
-
now apply ZF_sub_pair.
-
apply ZF_sub_pair; trivial.
Admitted.

Lemma ZF_eq_opair T x y x' y' : ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ opair x y ≡ opair x' y'.
Proof.
intros HT H1 H2.
Admitted.

Lemma ZF_sing_el x : ZFeq' ⊢ x ∈ sing x.
Proof.
apply ZF_pair_el.
apply DI1.
Admitted.

Lemma ZF_sing_iff T x y : ZFeq' <<= T -> T ⊢ x ∈ sing y <-> T ⊢ x ≡ y.
Proof.
intros HT.
unfold sing.
rewrite <- ZF_pair_el'; trivial.
split; intros H.
-
apply (DE H); auto.
-
Admitted.

Lemma ZF_union_el' T x y z : ZFeq' <<= T -> T ⊢ y ∈ x ∧ z ∈ y -> T ⊢ z ∈ ⋃ x.
Proof.
intros HT H.
assert (HU : T ⊢ ax_union) by (apply Ctx; firstorder).
apply (AllE x), (AllE z) in HU; cbn in HU.
subsimpl_in HU.
apply CE2 in HU.
eapply IE; try apply HU.
apply ExI with y.
cbn.
subsimpl.
Admitted.

Lemma ZF_union_el x y z : ZFeq' ⊢ y ∈ x ∧ z ∈ y -> ZFeq' ⊢ z ∈ ⋃ x.
Proof.
Admitted.

Lemma ZF_sub_union T x y : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ sub (⋃ x) (⋃ y).
Proof.
intros HT H.
prv_all z.
apply II.
assert1 H'.
assert (HU : (z ∈ ⋃ x :: T) ⊢ ax_union) by (apply Ctx; firstorder).
apply (AllE x), (AllE z) in HU; cbn in HU; subsimpl_in HU.
apply CE1 in HU.
eapply (IE HU) in H'.
use_exists H' u.
clear H' HU.
eapply ZF_union_el'; auto.
apply CI.
-
eapply ZF_eq_elem.
auto.
apply ZF_refl'; auto.
apply (Weak H); auto.
eapply CE1; auto.
-
Admitted.

Lemma ZF_eq_union T x y : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ ⋃ x ≡ ⋃ y.
Proof.
intros HT H.
apply ZF_ext'; try apply ZF_sub_union; trivial.
Admitted.

Lemma ZF_bunion_el' T x y z : ZFeq' <<= T -> T ⊢ (z ∈ x ∨ z ∈ y) -> T ⊢ z ∈ x ∪ y.
Proof.
intros HT H.
apply (DE H).
-
eapply ZF_union_el' with x.
auto.
apply CI; auto.
apply ZF_pair_el'.
auto.
apply DI1.
apply ZF_refl'.
auto.
-
eapply ZF_union_el' with y.
auto.
apply CI; auto.
apply ZF_pair_el'.
auto.
apply DI2.
apply ZF_refl'.
Admitted.

Lemma ZF_bunion_el x y z : ZFeq' ⊢ (z ∈ x ∨ z ∈ y) -> ZFeq' ⊢ z ∈ x ∪ y.
Proof.
Admitted.

Lemma ZF_bunion_inv' x y z : ZFeq' ⊢ z ∈ x ∪ y ~> z ∈ x ∨ z ∈ y.
Proof.
assert (TU : ZFeq' ⊢ ax_union) by (apply Ctx; firstorder).
unfold ax_union in TU.
eapply (AllE ({x; y})), (AllE z), CE1 in TU; cbn in TU; subsimpl_in TU.
rewrite imps in *.
use_exists TU u.
eapply DE.
apply ZF_pair_el'; auto.
-
eapply CE1.
auto.
-
apply DI1.
eapply ZF_eq_elem; auto.
+
apply ZF_refl'.
auto.
+
eapply CE2.
auto.
-
apply DI2.
eapply ZF_eq_elem; auto.
+
apply ZF_refl'.
auto.
+
eapply CE2.
Admitted.

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

Lemma prep_string_subst sigma s x : (prep_string s x)`[sigma] = prep_string s x`[sigma].
Proof.
induction s; cbn; trivial.
rewrite IHs.
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
auto.
