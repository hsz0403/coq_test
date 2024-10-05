Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.FullTarski_facts.
Require Import Undecidability.FOL.ZF.
Require Import Undecidability.FOL.Reductions.PCPb_to_ZF.
Require Import Lia.
From Undecidability.PCP Require Import PCP Util.PCP_facts Reductions.PCPb_iff_dPCPb.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Require Import Morphisms.
Section ZF.
Context { V : Type }.
Context { M : interp V }.
Hypothesis M_ZF : forall rho, rho ⊫ ZFeq'.
Definition set_equiv x y := x ≡ y.
Notation "x ≡' y" := (set_equiv x y) (at level 35).
Definition set_elem x y := x ∈ y.
Notation "x ∈' y" := (set_elem x y) (at level 35).
Definition set_sub x y := forall z, z ∈' x -> z ∈' y.
Notation "x ⊆' y" := (set_sub x y) (at level 35).
Instance set_equiv_equiv : Equivalence set_equiv.
Proof.
split.
-
apply (@M_ZF (fun _ => ∅) ax_refl).
cbn; tauto.
-
apply (@M_ZF (fun _ => ∅) ax_sym).
cbn; tauto.
-
apply (@M_ZF (fun _ => ∅) ax_trans).
cbn; tauto.
Instance set_equiv_elem : Proper (set_equiv ==> set_equiv ==> iff) set_elem.
Proof.
intros x x' Hx y y' Hy.
split.
-
apply (@M_ZF (fun _ => ∅) ax_eq_elem); cbn; tauto.
-
symmetry in Hx, Hy.
apply (@M_ZF (fun _ => ∅) ax_eq_elem); cbn; tauto.
Instance set_equiv_sub : Proper (set_equiv ==> set_equiv ==> iff) set_sub.
Proof.
intros x x' Hx y y' Hy.
unfold set_sub.
setoid_rewrite Hx.
setoid_rewrite Hy.
tauto.
Hint Resolve set_equiv_refl set_equiv_refl' : core.
Definition pair x y := {x; y}.
Instance set_equiv_pair : Proper (set_equiv ==> set_equiv ==> set_equiv) pair.
Proof.
intros x x' Hx y y' Hy.
unfold pair.
apply M_ext; unfold set_sub.
all: setoid_rewrite M_pair.
all: setoid_rewrite Hx; setoid_rewrite Hy; tauto.
Instance set_equiv_opair : Proper (set_equiv ==> set_equiv ==> set_equiv) M_opair.
Proof.
intros x x' Hx y y' Hy.
unfold M_opair.
change ({pair x x; pair x y} ≡' {pair x' x'; pair x' y'}).
apply M_ext; unfold set_sub.
all: setoid_rewrite M_pair.
all: setoid_rewrite Hx; setoid_rewrite Hy; tauto.
Definition union x := ⋃ x.
Instance equiv_union : Proper (set_equiv ==> set_equiv) union.
Proof.
intros x x' Hx.
unfold union.
apply M_ext; unfold set_sub.
all: setoid_rewrite M_union.
all: setoid_rewrite Hx; tauto.
Definition power x := PP x.
Instance equiv_power : Proper (set_equiv ==> set_equiv) power.
Proof.
intros x x' Hx.
unfold power.
apply M_ext; unfold set_sub.
all: setoid_rewrite M_power.
all: setoid_rewrite Hx; tauto.
Definition M_binunion x y := ⋃ {x; y}.
Notation "x ∪' y" := (M_binunion x y) (at level 32).
Instance equiv_bunion : Proper (set_equiv ==> set_equiv ==> set_equiv) M_binunion.
Proof.
intros x x' Hx y y' Hy.
unfold M_binunion.
apply M_ext; unfold set_sub.
all: setoid_rewrite binunion_el.
all: setoid_rewrite Hx; setoid_rewrite Hy; tauto.
Hint Resolve binunionl binunionr : core.
Instance equiv_prep : Proper (eq ==> set_equiv ==> set_equiv) M_prep_string.
Proof.
intros s s' <- x x' Hx.
induction s; cbn; trivial.
now rewrite IHs.
Definition M_comb_rel s t := fun u v => exists u1 u2, u ≡' M_opair u1 u2 /\ v ≡' M_opair (M_prep_string s u1) (M_prep_string t u2).
Fixpoint M_combinations B x y := match B with | nil => y = ∅ | (s,t)::B => exists y1 y2, y ≡' y2 ∪ y1 /\ M_combinations B x y1 /\ M_is_rep (M_comb_rel s t) x y2 end.
Definition M_solutions B f n := M_opair ∅ (M_enc_stack B) ∈' f /\ forall k x y, k ∈' n -> M_opair k x ∈' f -> M_combinations B x y -> M_opair (σ k) y ∈' f.
Instance equiv_solutions : Proper (eq ==> eq ==> set_equiv ==> iff) M_solutions.
Proof.
intros B B' <- f f' <- x x' Hx.
unfold M_solutions.
setoid_rewrite Hx.
tauto.
Definition M_function f := forall x y y', M_opair x y ∈ f -> M_opair x y' ∈ f -> y ≡' y'.
End ZF.

Lemma opair_inj1 x x' y y' : M_opair x y ≡' M_opair x' y' -> x ≡' x'.
Proof.
intros He.
assert (H : {x; x} ∈' M_opair x y) by apply M_pair1.
rewrite He in H.
apply M_pair in H as [H|H]; apply (sing_pair H).
