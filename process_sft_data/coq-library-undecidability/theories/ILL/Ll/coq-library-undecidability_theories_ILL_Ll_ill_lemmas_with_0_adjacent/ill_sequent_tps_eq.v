Require Import List Permutation Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec.
From Undecidability.ILL Require Import ILL.
Set Implicit Arguments.
Section obvious_links_between_fragments.
Notation "P ⇒ Q" := (forall Γ A, P Γ A -> Q Γ A) (at level 70).
Fact S_ill_restr_restr_wc : S_ill_restr ⇒ S_ill_restr_wc.
Proof.
induction 1.
all: try now constructor.
now constructor 3 with (Γ := Γ).
Fact S_ill_full_wc : S_ill ⇒ S_ill_wc.
Proof.
induction 1.
all: try now constructor.
now constructor 3 with (Γ := Γ).
Fact S_ill_restr_full : S_ill_restr ⇒ S_ill.
Proof.
induction 1.
all: try now constructor.
now constructor 2 with (Γ := Γ).
Fact S_ill_restr_full_wc : S_ill_restr_wc ⇒ S_ill_wc.
Proof.
induction 1.
all: try now constructor.
+
now constructor 2 with A.
+
now constructor 3 with (Γ := Γ).
End obvious_links_between_fragments.
Local Notation "Γ '⊢r' A" := (S_ill_restr Γ A) (at level 70, no associativity).
Local Notation "Γ '⊢' A" := (S_ill_wc Γ A) (at level 70, no associativity).
Fact S_ill_restr_weak Γ Δ B : Δ ⊢r B -> ‼Γ++Δ ⊢r B.
Proof.
intro; induction Γ; simpl; auto; apply in_ill1_weak; auto.
Fact S_ill_wc_weak Γ Δ B : Δ ⊢ B -> ‼Γ++Δ ⊢ B.
Proof.
intro; induction Γ; simpl; auto; apply in_ill4_weak; auto.
Fact S_ill_restr_cntr Γ Δ B : ‼Γ++‼Γ++Δ ⊢r B -> ‼Γ++ Δ ⊢r B.
Proof.
revert Γ Δ; intros Ga.
induction Ga as [ | A Ga IH ]; simpl; auto; intros De.
intros H.
apply in_ill1_cntr.
apply in_ill1_perm with (‼Ga ++ (!A::!A::De)).
+
apply Permutation_sym.
do 2 apply Permutation_cons_app; auto.
+
apply IH.
revert H; apply in_ill1_perm.
rewrite app_assoc.
apply Permutation_cons_app.
rewrite <- app_assoc.
apply Permutation_app; auto.
apply Permutation_cons_app; auto.
Fact S_ill_wc_cntr Γ Δ B : ‼Γ++‼Γ++Δ ⊢ B -> ‼Γ++ Δ ⊢ B.
Proof.
revert Γ Δ; intros Ga.
induction Ga as [ | A Ga IH ]; simpl; auto; intros De.
intros H.
apply in_ill4_cntr.
apply in_ill4_perm with (‼Ga ++ (!A::!A::De)).
+
apply Permutation_sym.
do 2 apply Permutation_cons_app; auto.
+
apply IH.
revert H; apply in_ill4_perm.
rewrite app_assoc.
apply Permutation_cons_app.
rewrite <- app_assoc.
apply Permutation_app; auto.
apply Permutation_cons_app; auto.
Section trivial_phase_semantics.
Variables (n : nat) (s : ill_vars -> vec nat n -> Prop).
Reserved Notation "'⟦' A '⟧'" (at level 65).
Definition ill_tps_imp (X Y : _ -> Prop) (v : vec _ n) := forall x, X x -> Y (vec_plus x v).
Definition ill_tps_mult (X Y : _ -> Prop) (x : vec _ n) := exists a b, x = vec_plus a b /\ X a /\ Y b.
Infix "**" := ill_tps_mult (at level 65, right associativity).
Infix "-*" := ill_tps_imp (at level 65, right associativity).
Fact ll_tps_mult_mono (X1 X2 Y1 Y2 : _ -> Prop) : (forall x, X1 x -> X2 x) -> (forall x, Y1 x -> Y2 x) -> (forall x, (X1**Y1) x -> (X2**Y2) x).
Proof.
intros H1 H2 x (a & b & H3 & H4 & H5); subst.
exists a, b; auto.
Fixpoint ill_tps A x : Prop := match A with | £ X => s X x | A & B => ⟦A⟧ x /\ ⟦B⟧ x | !A => ⟦A⟧ x /\ x = vec_zero | A ⊸ B => (⟦A⟧ -* ⟦B⟧) x | A ⊗ B => (⟦A⟧ ** ⟦B⟧) x | A ⊕ B => ⟦A⟧ x \/ ⟦B⟧ x | ⟘ => False | ⟙ => True | 𝝐 => x = vec_zero end where "⟦ A ⟧" := (ill_tps A).
Reserved Notation "'[[' Γ ']]'" (at level 0).
Fixpoint ill_tps_list Γ := match Γ with | ∅ => eq vec_zero | A::Γ => ⟦A⟧ ** [[Γ]] end where "[[ Γ ]]" := (ill_tps_list Γ).
Fact ill_tps_app Γ Δ x : [[Γ++Δ]] x <-> ([[Γ]]**[[Δ]]) x.
Proof.
revert Γ Δ x; intros Ga De.
induction Ga as [ | A Ga IH ]; intros x; simpl; split; intros Hx.
+
exists vec_zero, x; simpl; rew vec.
+
destruct Hx as (a & b & H1 & H2 & H3); subst; auto; rewrite vec_zero_plus; auto.
+
destruct Hx as (a & b & H1 & H2 & H3).
apply IH in H3.
destruct H3 as (c & d & H4 & H5 & H6).
exists (vec_plus a c), d; split.
*
subst; apply vec_plus_assoc.
*
split; auto.
exists a, c; auto.
+
destruct Hx as (y & d & H1 & H2 & H3).
destruct H2 as (a & g & H2 & H4 & H5).
exists a, (vec_plus g d); split.
*
subst; symmetry; apply vec_plus_assoc.
*
split; auto.
apply IH.
exists g, d; auto.
Fact ill_tps_lbang Γ x : [[‼Γ]] x <-> [[Γ]] x /\ x = vec_zero.
Proof.
revert Γ x; intros Ga.
induction Ga as [ | A Ga IH ]; intros x.
+
simpl; split; auto; tauto.
+
split.
*
intros (a & g & H1 & H2 & H3).
split.
-
exists a, g; repeat split; auto.
**
apply H2.
**
apply IH; auto.
-
apply IH, proj2 in H3.
apply proj2 in H2; subst; auto.
apply vec_zero_plus.
*
intros ((a & g & H1 & H2 & H3) & H4).
exists x, x.
assert (a = vec_zero /\ g = vec_zero) as E.
{
apply vec_plus_is_zero; subst; auto.
}
destruct E; subst; repeat split; auto; rew vec.
apply IH; auto.
Fact ill_tps_list_bang_zero Γ : [[‼Γ]] vec_zero <-> forall A, In A Γ -> ⟦A⟧ vec_zero.
Proof.
induction Γ as [ | A Ga IH ].
+
split.
*
simpl; tauto.
*
intros _; simpl; auto.
+
split.
*
intros (u & v & H1 & H2 & H3).
destruct H2 as [ H2 H4 ]; subst; auto.
rewrite vec_zero_plus in H1; subst.
rewrite IH in H3.
intros B [ E | HB ]; subst; auto.
*
intros H.
exists vec_zero, vec_zero.
rewrite vec_zero_plus; repeat split; auto.
-
apply H; left; auto.
-
rewrite IH.
intros; apply H; right; auto.
Fact ill_tps_perm Γ Δ : Γ ~p Δ -> forall x, [[Γ]] x -> [[Δ]] x.
Proof.
induction 1 as [ | A Ga De H IH | A B Ga | ]; simpl; auto.
+
intros x (a & b & H1 & H2 & H3).
exists a, b; repeat split; auto.
+
intros x (a & b & H1 & H2 & c & d & H3 & H4 & H5).
exists c, (vec_plus a d); split.
*
subst; rewrite (vec_plus_comm c), vec_plus_assoc, (vec_plus_comm c); auto.
*
split; auto.
exists a, d; auto.
Definition ill_sequent_tps Γ A := [[Γ]] -* ⟦A⟧.
Notation "'[<' Γ '|-' A '>]'" := (ill_sequent_tps Γ A).
Fact ill_sequent_tps_mono Γ A B : (forall x, ⟦A⟧ x -> ⟦B⟧ x) -> forall x, [< Γ |- A >] x -> [< Γ |- B >] x.
Proof.
intros H x; simpl; unfold ill_sequent_tps.
intros H1 a H2.
apply H, H1; auto.
Fact ill_perm_tps Γ Δ : Γ ~p Δ -> forall x A, [< Γ |- A >] x -> [< Δ |- A >] x.
Proof.
intros H1 x B; unfold ill_sequent_tps.
intros H2 a H3.
apply H2; revert H3.
apply ill_tps_perm, Permutation_sym; auto.
Fact ill_sequent_tps_eq Γ A : [< Γ |- A >] vec_zero <-> forall x, [[Γ]] x -> ⟦A⟧ x.
Proof.
split.
*
intros H x Hx.
rewrite <- vec_zero_plus, vec_plus_comm.
apply (H x); trivial.
*
intros H x Hx.
rewrite vec_plus_comm, vec_zero_plus; auto.
End trivial_phase_semantics.

Fact ill_sequent_tps_eq Γ A : [< Γ |- A >] vec_zero <-> forall x, [[Γ]] x -> ⟦A⟧ x.
Proof.
split.
*
intros H x Hx.
rewrite <- vec_zero_plus, vec_plus_comm.
apply (H x); trivial.
*
intros H x Hx.
rewrite vec_plus_comm, vec_zero_plus; auto.
