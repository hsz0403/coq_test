Require Import List Permutation.
From Undecidability.ILL Require Import ILL.
Set Implicit Arguments.
Local Infix "~p" := (@Permutation _) (at level 70).
Notation eill_vars := nat.
Inductive eill_cmd : Set := | in_eill_cmd_inc : eill_vars -> eill_vars -> eill_vars -> eill_cmd | in_eill_cmd_dec : eill_vars -> eill_vars -> eill_vars -> eill_cmd | in_eill_cmd_fork : eill_vars -> eill_vars -> eill_vars -> eill_cmd.
Notation LL_INC := in_eill_cmd_inc.
Notation LL_DEC := in_eill_cmd_dec.
Notation LL_FORK := in_eill_cmd_fork.
Definition eill_cmd_vars c := match c with | LL_INC a p q => a::p::q::nil | LL_DEC a p q => a::p::q::nil | LL_FORK p q r => p::q::r::nil end.
Definition eill_cmd_map c := match c with | LL_INC a p q => (£a ⊸ £p) ⊸ £ q | LL_DEC a p q => £a ⊸ £p ⊸ £ q | LL_FORK p q r => (£p & £q) ⊸ £ r end.
Section GeILL.
Reserved Notation "Σ ; Γ ⊦ u" (at level 70, no associativity).
Inductive G_eill (Σ : list eill_cmd) : list eill_vars -> eill_vars -> Prop := | in_geill_ax : forall u, Σ; u::∅ ⊦ u | in_geill_perm : forall Γ Δ p, Γ ~p Δ -> Σ; Γ ⊦ p -> Σ; Δ ⊦ p | in_geill_inc : forall Γ a p q, In (LL_INC a p q) Σ -> Σ; a::Γ ⊦ p -> Σ; Γ ⊦ q | in_geill_dec : forall Γ Δ p q r, In (LL_DEC p q r) Σ -> Σ; Γ ⊦ p -> Σ; Δ ⊦ q -> Σ; Γ++Δ ⊦ r | in_geill_fork : forall Γ p q r, In (LL_FORK p q r) Σ -> Σ; Γ ⊦ p -> Σ; Γ ⊦ q -> Σ; Γ ⊦ r where "Σ ; Γ ⊦ u" := (G_eill Σ Γ u).
End GeILL.
Definition EILL_SEQUENT := (list eill_cmd * list eill_vars * eill_vars)%type.
Definition EILL_PROVABILITY (c : EILL_SEQUENT) := match c with (Σ,Γ,u) => G_eill Σ Γ u end.