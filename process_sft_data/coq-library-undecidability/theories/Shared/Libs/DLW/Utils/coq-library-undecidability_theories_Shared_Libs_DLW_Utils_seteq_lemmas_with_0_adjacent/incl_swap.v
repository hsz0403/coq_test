Require Import Arith Lia List Permutation.
From Undecidability.Shared.Libs.DLW.Utils Require Import php.
From Undecidability.Shared.Libs.DLW.Wf Require Import measure_ind.
Set Implicit Arguments.
Reserved Notation "x ≡ y" (at level 70, no associativity).
Reserved Notation "x ⊆ y" (at level 70, no associativity).
Local Infix "~p" := (@Permutation _) (at level 70, no associativity).
Section seteq.
Variable X : Type.
Inductive seteq : list X -> list X -> Prop := | seteq_nil : nil ≡ nil | seteq_skip : forall x l m, l ≡ m -> x::l ≡ x::m | seteq_swap : forall x y l, x::y::l ≡ y::x::l | seteq_dup : forall x l, x::x::l ≡ x::l | seteq_sym : forall l m, l ≡ m -> m ≡ l | seteq_trans : forall l m k, l ≡ m -> m ≡ k -> l ≡ k where "l ≡ m" := (seteq l m).
Hint Constructors seteq : core.
Fact perm_seteq l m : l ~p m -> l ≡ m.
Proof.
induction 1; eauto.
Notation "l ⊆ m" := (incl l m).
Fact incl_cons_mono (x : X) l m : l ⊆ m -> x::l ⊆ x::m.
Proof.
intros ? ? [ -> | ]; simpl; auto.
Fact incl_swap (x y : X) l : x::y::l ⊆ y::x::l.
Proof.
intros ? [ -> | [ -> | ] ]; simpl; auto.
Fact incl_cntr (x : X) l : x::x::l ⊆ x::l.
Proof.
intros ? [ -> | [ -> | ] ]; simpl; auto.
Hint Resolve incl_refl incl_cons_mono incl_swap incl_cntr incl_tl : core.
Fact seqeq_incl l m : l ≡ m -> l ⊆ m /\ m ⊆ l.
Proof.
induction 1 as [ | x l m H [] | x y l | x l | l m H [] | l m k H1 IH1 H2 IH2 ]; auto.
split; apply incl_tran with m; tauto.
Hint Resolve seqeq_incl incl_seteq : core.
End seteq.
Local Infix "≡" := seteq.
Local Infix "⊆" := incl.

Fact incl_swap (x y : X) l : x::y::l ⊆ y::x::l.
Proof.
intros ? [ -> | [ -> | ] ]; simpl; auto.
