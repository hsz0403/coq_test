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

Lemma set_equiv_refl x : x ≡ x.
Proof.
Admitted.

Lemma M_ext x y : x ⊆' y -> y ⊆' x -> x ≡' y.
Proof.
apply (@M_ZF (fun _ => ∅) ax_ext).
Admitted.

Lemma M_eset x : ~ x ∈' ∅.
Proof.
refine (@M_ZF (fun _ => ∅) ax_eset _ x).
Admitted.

Lemma M_pair x y z : x ∈' {y; z} <-> x ≡' y \/ x ≡' z.
Proof.
apply (@M_ZF (fun _ => ∅) ax_pair).
Admitted.

Instance set_equiv_pair : Proper (set_equiv ==> set_equiv ==> set_equiv) pair.
Proof.
intros x x' Hx y y' Hy.
unfold pair.
apply M_ext; unfold set_sub.
all: setoid_rewrite M_pair.
Admitted.

Instance set_equiv_opair : Proper (set_equiv ==> set_equiv ==> set_equiv) M_opair.
Proof.
intros x x' Hx y y' Hy.
unfold M_opair.
change ({pair x x; pair x y} ≡' {pair x' x'; pair x' y'}).
apply M_ext; unfold set_sub.
all: setoid_rewrite M_pair.
Admitted.

Lemma M_union x y : x ∈' ⋃ y <-> exists z, z ∈' y /\ x ∈' z.
Proof.
apply (@M_ZF (fun _ => ∅) ax_union).
Admitted.

Instance equiv_union : Proper (set_equiv ==> set_equiv) union.
Proof.
intros x x' Hx.
unfold union.
apply M_ext; unfold set_sub.
all: setoid_rewrite M_union.
Admitted.

Lemma M_power x y : x ∈' PP y <-> x ⊆' y.
Proof.
apply (@M_ZF (fun _ => ∅) ax_power).
Admitted.

Instance equiv_power : Proper (set_equiv ==> set_equiv) power.
Proof.
intros x x' Hx.
unfold power.
apply M_ext; unfold set_sub.
all: setoid_rewrite M_power.
Admitted.

Lemma M_om1 : M_inductive ω.
Proof.
apply (@M_ZF (fun _ => ∅) ax_om1).
Admitted.

Lemma M_om2 x : M_inductive x -> ω ⊆ x.
Proof.
apply (@M_ZF (fun _ => ∅) ax_om2).
Admitted.

Lemma binunion_el x y z : x ∈' y ∪ z <-> x ∈' y \/ x ∈' z.
Proof.
split.
-
intros [u [H1 H2]] % M_union.
apply M_pair in H1 as [<-| <-]; auto.
-
intros [H|H].
+
apply M_union.
exists y.
rewrite M_pair.
auto.
+
apply M_union.
exists z.
rewrite M_pair.
Admitted.

Instance equiv_bunion : Proper (set_equiv ==> set_equiv ==> set_equiv) M_binunion.
Proof.
intros x x' Hx y y' Hy.
unfold M_binunion.
apply M_ext; unfold set_sub.
all: setoid_rewrite binunion_el.
Admitted.

Lemma sing_el x y : x ∈' M_sing y <-> x ≡' y.
Proof.
split.
-
now intros [H|H] % M_pair.
-
intros ->.
apply M_pair.
Admitted.

Lemma M_pair1 x y : x ∈' {x; y}.
Proof.
apply M_pair.
Admitted.

Lemma M_pair2 x y : y ∈' {x; y}.
Proof.
apply M_pair.
Admitted.

Lemma sing_pair x y z : {x; x} ≡' {y; z} -> x ≡' y /\ x ≡' z.
Proof.
intros He.
split.
-
assert (H : y ∈' {y; z}) by apply M_pair1.
rewrite <- He in H.
apply M_pair in H.
intuition.
-
assert (H : z ∈' {y; z}) by apply M_pair2.
rewrite <- He in H.
apply M_pair in H.
Admitted.

Lemma opair_inj1 x x' y y' : M_opair x y ≡' M_opair x' y' -> x ≡' x'.
Proof.
intros He.
assert (H : {x; x} ∈' M_opair x y) by apply M_pair1.
rewrite He in H.
Admitted.

Lemma opair_inj2 x x' y y' : M_opair x y ≡' M_opair x' y' -> y ≡' y'.
Proof.
intros He.
assert (y ≡' x' \/ y ≡' y') as [Hy | Hy]; trivial.
-
assert (H : {x; y} ∈' M_opair x y) by apply M_pair2.
rewrite He in H.
apply M_pair in H as [H|H].
+
symmetry in H.
apply sing_pair in H.
intuition.
+
assert (H' : y ∈' {x; y}) by apply M_pair2.
rewrite H in H'.
now apply M_pair in H'.
-
assert (Hx : x ≡' x') by now apply opair_inj1 in He.
rewrite Hx, Hy in He.
rewrite Hy.
assert (H : {x'; y'} ∈' M_opair x' y') by apply M_pair2.
rewrite <- He in H.
Admitted.

Lemma sigma_el x y : x ∈' σ y <-> x ∈' y \/ x ≡' y.
Proof.
split.
-
intros [H|H] % binunion_el; auto.
apply sing_el in H.
now right.
-
intros [H| ->]; apply binunion_el; auto.
right.
Admitted.

Lemma binunion_eset x : x ≡' ∅ ∪ x.
Proof.
apply M_ext.
-
intros y H.
apply binunion_el.
now right.
-
intros y [H|H] % binunion_el.
+
now apply M_eset in H.
+
Admitted.

Lemma pair_com x y : {x; y} ≡' {y; x}.
Proof.
Admitted.

Lemma binunion_com x y : x ∪' y ≡' y ∪' x.
Proof.
Admitted.

Lemma binunionl a x y : a ∈' x -> a ∈' x ∪' y.
Proof.
intros H.
apply binunion_el.
Admitted.

Lemma binunionr a x y : a ∈' y -> a ∈' x ∪' y.
Proof.
intros H.
apply binunion_el.
Admitted.

Lemma binunion_assoc x y z : (x ∪' y) ∪' z ≡' x ∪' (y ∪' z).
Proof.
apply M_ext; intros a [H|H] % binunion_el; eauto.
-
apply binunion_el in H as [H|H]; eauto.
-
Admitted.

Lemma numeral_lt k l : k < l -> numeral k ∈ numeral l.
Proof.
Admitted.

Lemma enc_bool_inj b c : M_enc_bool b ≡' M_enc_bool c -> b = c.
Proof.
destruct b, c; trivial; cbn.
-
intros H.
contradiction (@M_eset ∅).
rewrite <- H at 2.
apply M_pair; auto.
-
intros H.
contradiction (@M_eset ∅).
rewrite H at 2.
Admitted.

Lemma enc_string_inj s t : M_enc_string s ≡' M_enc_string t -> s = t.
Proof.
induction s in t|-*; destruct t as [|b t]; cbn; trivial.
-
intros H.
contradiction (M_eset (x:=M_sing (M_enc_bool b))).
rewrite H.
apply M_pair.
now left.
-
intros H.
contradiction (M_eset (x:=M_sing (M_enc_bool a))).
rewrite <- H.
apply M_pair.
now left.
-
intros [H1 H2] % opair_inj.
apply IHs in H2 as ->.
apply enc_bool_inj in H1 as ->.
Admitted.

Instance equiv_prep : Proper (eq ==> set_equiv ==> set_equiv) M_prep_string.
Proof.
intros s s' <- x x' Hx.
induction s; cbn; trivial.
Admitted.

Lemma M_enc_stack_app A B : M_enc_stack (A ++ B) ≡' M_enc_stack A ∪' M_enc_stack B.
Proof.
induction A as [|[s t] A IH]; cbn.
-
apply binunion_eset.
-
change (M_enc_stack (A ++ B) ∪' M_sing (M_enc_card s t) ≡' (M_enc_stack A ∪' M_sing (M_enc_card s t)) ∪' M_enc_stack B).
rewrite IH.
rewrite !binunion_assoc.
Admitted.

Lemma enc_stack_el' x A : x ∈ M_enc_stack A -> exists s t, (s, t) el A /\ x ≡' M_enc_card s t.
Proof.
induction A as [|[s t] A IH]; cbn.
-
now intros H % M_eset.
-
intros [H|H] % binunion_el.
+
destruct (IH H) as (u&v&H1&H2).
exists u, v.
intuition.
+
apply sing_el in H.
exists s, t.
Admitted.

Lemma enc_stack_el B s t : (s, t) el B -> M_enc_card s t ∈ M_enc_stack B.
Proof.
induction B as [|[u b] B IH]; cbn; auto.
intros [H|H]; apply binunion_el.
-
right.
apply sing_el.
injection H.
now intros -> ->.
-
left.
Admitted.

Lemma M_combinations_spec B rho x y a b : M_combinations B x y -> eval rho a = x -> eval rho b = y -> rho ⊨ combinations B a b.
Proof.
induction B in y,a,b,rho|-*; cbn.
-
now intros -> _ ->.
-
destruct a0 as [s t].
intros (y1&y2&H1&H2&H3) Ha Hb.
exists y1, y2.
repeat split.
+
cbn.
erewrite !eval_comp.
unfold funcomp.
cbn.
change (eval rho b ≡' y2 ∪ y1).
now rewrite Hb, H1.
+
eapply (IHB _ y1); trivial.
erewrite !eval_comp.
unfold funcomp.
cbn.
change (eval (fun x => rho x) a) with (eval rho a).
now rewrite Ha.
+
intros (u & Hu & c & d' & H) % H3.
exists u.
split.
*
cbn.
erewrite !eval_comp.
erewrite eval_ext, Ha; trivial.
*
exists d', c.
cbn.
rewrite !eval_prep_string.
apply H.
+
intros (u & Hu & c & d' & H).
apply H3.
exists u.
split.
*
cbn in Hu.
erewrite !eval_comp in Hu.
rewrite <- Ha.
apply Hu.
*
exists d', c.
cbn in H.
rewrite !eval_prep_string in H.
Admitted.

Instance equiv_solutions : Proper (eq ==> eq ==> set_equiv ==> iff) M_solutions.
Proof.
intros B B' <- f f' <- x x' Hx.
unfold M_solutions.
setoid_rewrite Hx.
Admitted.

Lemma comb_rel_rep C s t : M_is_rep (M_comb_rel s t) (M_enc_stack C) (M_enc_stack (append_all C (s, t))).
Proof.
intros y.
split.
-
intros (u&v&H&H') % enc_stack_el'.
unfold append_all in H.
apply in_map_iff in H as [[a b][H1 H2]].
cbn in H1.
exists (M_enc_card a b).
split; try now apply enc_stack_el.
exists (M_enc_string a), (M_enc_string b).
split; trivial.
assert (u = s++a) as -> by congruence.
assert (v = t++b) as -> by congruence.
now rewrite !M_prep_enc.
-
intros (u&H&a&b&H3&H4).
apply enc_stack_el' in H as [u'[v[H1 H2]]].
rewrite H3 in H2.
apply opair_inj in H2 as [H2 H2'].
change (y ∈' M_enc_stack (append_all C (s, t))).
rewrite H4, H2, H2', !M_prep_enc.
apply enc_stack_el.
apply in_map_iff.
Admitted.

Lemma M_combinations_step B C : M_combinations B (M_enc_stack C) (M_enc_stack (derivation_step B C)).
Proof.
induction B as [|[s t] B IH]; cbn; trivial.
exists (M_enc_stack (derivation_step B C)), (M_enc_stack (append_all C (s, t))).
rewrite M_enc_stack_app.
split; trivial.
split; trivial.
Admitted.

Lemma solutions_derivations B f n k : M_solutions B f (numeral n) -> k <= n -> M_opair (numeral k) (M_enc_stack (derivations B k)) ∈ f.
Proof.
intros H Hk; induction k; cbn.
-
apply H.
-
assert (Hk' : k <= n) by lia.
specialize (IHk Hk').
destruct H as [_ H].
eapply H in IHk; eauto.
+
now apply numeral_lt.
+
Admitted.

Lemma M_solutions_el B f k X p : standard M -> k ∈ ω -> M_function f -> M_solutions B f k -> M_opair k X ∈' f -> p ∈' X -> exists u v, p ≡' M_enc_card u v /\ derivable B u v.
Proof.
intros HS HO Hf Hk HX Hp.
destruct (HS k HO) as [n Hn].
change (k ≡' numeral n) in Hn.
rewrite Hn in Hk.
rewrite Hn in HX.
pose proof (H := solutions_derivations Hk (le_n n)).
rewrite (Hf _ _ _ HX H) in Hp.
apply enc_stack_el' in Hp as (s&t&H'&Hp).
exists s, t.
split; trivial.
Admitted.

Lemma opair_inj x x' y y' : M_opair x y ≡' M_opair x' y' -> x ≡' x' /\ y ≡' y'.
Proof.
intros H.
split.
-
eapply opair_inj1; eassumption.
-
eapply opair_inj2; eassumption.
