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

Lemma ZF_eset x : ZFeq' ⊢ ¬ (x ∈ ∅).
Proof.
change (ZFeq' ⊢ (¬ ($0 ∈ ∅))[x..]).
apply AllE.
apply Ctx.
Admitted.

Lemma ZF_numeral n : ZFeq' ⊢ tnumeral n ∈ ω.
Proof.
induction n; cbn.
-
eapply CE1.
apply Ctx.
firstorder.
-
eapply IE; try apply IHn.
change (ZFeq' ⊢ ($0 ∈ ω ~> σ ($0) ∈ ω)[(tnumeral n)..]).
apply AllE.
eapply CE2.
apply Ctx.
Admitted.

Lemma ZF_refl' T x : ZFeq' <<= T -> T ⊢ x ≡ x.
Proof.
intros H.
change (T ⊢ ($0 ≡ $0)[x..]).
apply AllE.
apply Ctx.
Admitted.

Lemma ZF_refl x : ZFeq' ⊢ x ≡ x.
Proof.
Admitted.

Lemma ZF_sym' T x y : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ x.
Proof.
intros H1 H2.
eapply IE; try apply H2.
assert (H : T ⊢ ax_sym) by (apply Ctx; firstorder).
apply (AllE x), (AllE y) in H; cbn in H.
Admitted.

Lemma ZF_trans' T x y z : ZFeq' <<= T -> T ⊢ x ≡ y -> T ⊢ y ≡ z -> T ⊢ x ≡ z.
Proof.
intros H1 H2 H3.
eapply IE; try apply H3.
eapply IE; try apply H2.
assert (H : T ⊢ ax_trans) by (apply Ctx; firstorder).
Admitted.

Lemma ZF_eq_elem T x y x' y' : ZFeq' <<= T -> T ⊢ x ≡ x' -> T ⊢ y ≡ y' -> T ⊢ x ∈ y -> T ⊢ x' ∈ y'.
Proof.
intros H1 H2 H3 H4.
eapply IE; try apply H4.
eapply IE; try apply H3.
eapply IE; try apply H2.
assert (H : T ⊢ ax_eq_elem) by (apply Ctx; firstorder).
Admitted.

Lemma ZF_ext' T x y : ZFeq' <<= T -> T ⊢ sub x y -> T ⊢ sub y x -> T ⊢ x ≡ y.
Proof.
intros H1 H2 H3.
eapply IE; try apply H3.
eapply IE; try apply H2.
assert (H : T ⊢ ax_ext) by (apply Ctx; firstorder).
apply (AllE x), (AllE y) in H; cbn in H.
subsimpl_in H.
Admitted.

Lemma ZF_pair_el' T x y z : ZFeq' <<= T -> T ⊢ (z ≡ x ∨ z ≡ y) <-> T ⊢ z ∈ {x; y}.
Proof.
intros HT; split; intros H; eapply IE; try apply H.
all: assert (HP : T ⊢ ax_pair) by (apply Ctx; firstorder).
all: apply (AllE y), (AllE x), (AllE z) in HP; cbn in HP; subsimpl_in HP.
-
eapply CE2, HP.
-
Admitted.

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

Lemma ZF_eset' T x : ZFeq' <<= T -> T ⊢ ¬ (x ∈ ∅).
Proof.
intros H.
now apply (Weak (ZF_eset x)).
