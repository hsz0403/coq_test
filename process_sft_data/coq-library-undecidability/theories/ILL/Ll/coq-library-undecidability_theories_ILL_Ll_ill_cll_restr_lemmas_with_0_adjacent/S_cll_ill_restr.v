Require Import List Permutation Arith.
From Undecidability.ILL Require Import ILL CLL ill_cll.
Set Implicit Arguments.
Fact app_eq_single_inv X (l m : list X) x : l++m = x::nil -> l = nil /\ m = x::nil \/ l = x::nil /\ m = nil.
Proof.
intros H.
destruct l as [ | y l ]; auto.
right.
inversion H.
destruct l; destruct m; auto; discriminate.
Tactic Notation "app" "inv" "singleton" "in" hyp(H) := apply app_eq_single_inv in H as [ (-> & ->) | (-> & ->) ].
Tactic Notation "app" "inv" "nil" "in" hyp(H) := apply app_eq_nil in H as (-> & ->).
Local Infix "~p" := (@Permutation _) (at level 70).
Section S_ill_cll_restr.
Notation "Γ '⊢i' A" := (S_ill_restr Γ A) (at level 70).
Notation "Γ '⊢c' Δ" := (S_cll_restr Γ Δ) (at level 70).
Hint Resolve Permutation_map : core.
Let cll_ill_empty_rec Γ Δ : Γ ⊢c Δ -> Δ <> ∅.
Proof.
induction 1 as [ A (* ax *) | Γ Δ Γ' Δ' H1 H2 H3 IH3 (* perm *) | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1 (* -o *) | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2 (* & *) | Γ A Δ H1 IH1 | Γ A H1 IH1 (* bang *) | Γ A Δ H1 IH1 (* weak *) | Γ A Δ H1 IH1 ]; (* cntr *) auto; try discriminate.
+
intros ->; now apply IH3, Permutation_nil, Permutation_sym.
+
intros H; now app inv nil in H.
Let cll_ill_empty Γ : ~ Γ ⊢c ∅.
Proof.
intros H; now apply cll_ill_empty_rec with (1 := H).
Let cll_ill_rec Γ Δ : Γ ⊢c Δ -> forall A, Δ = A::∅ -> ⟪Γ⟫ ⊢i ⟨A⟩.
Proof.
induction 1 as [ A (* ax *) | Γ Δ Γ' Δ' H1 H2 H3 IH3 (* perm *) | Γ Δ Γ' Δ' A B H1 IH1 H2 IH2 | Γ Δ A B H1 IH1 (* -o *) | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 | Γ Δ A B H1 IH1 H2 IH2 (* & *) | Γ A Δ H1 IH1 | Γ A H1 IH1 (* bang *) | Γ A Δ H1 IH1 (* weak *) | Γ A Δ H1 IH1 ]; (* cntr *) intros C HC; try discriminate.
+
inversion HC; constructor.
+
subst.
apply (Permutation_map cll_ill) in H1.
constructor 2 with (1 := H1).
apply Permutation_sym, Permutation_length_1_inv in H2 as ->.
apply IH3; auto.
+
app inv singleton in HC.
*
simpl; rewrite map_app; constructor; auto.
*
apply cll_ill_empty in H2 as [].
+
inversion HC; subst.
constructor; apply IH1; auto.
+
rewrite HC in *.
apply in_ill1_with_l1, IH1; auto.
+
rewrite HC in *.
apply in_ill1_with_l2, IH1; auto.
+
inversion HC; subst; clear HC.
constructor; auto.
+
subst; constructor; apply IH1; auto.
+
inversion HC; subst.
rewrite cll_ill_lbang; simpl.
constructor.
rewrite <- cll_ill_lbang; auto.
+
subst; apply in_ill1_weak; auto.
+
subst; apply in_ill1_cntr; auto.
Hint Resolve S_ill_cll_restr S_cll_ill_restr : core.
End S_ill_cll_restr.

Theorem S_cll_ill_restr Γ A : Γ ⊢c A::∅ -> ⟪Γ⟫ ⊢i ⟨A⟩.
Proof.
intros H; now apply cll_ill_rec with (1 := H).
