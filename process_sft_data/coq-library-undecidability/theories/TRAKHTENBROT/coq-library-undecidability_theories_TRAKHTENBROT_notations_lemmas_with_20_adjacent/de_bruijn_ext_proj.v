Require Import List.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
Set Implicit Arguments.
Definition de_bruijn_ext {X} (ν : nat -> X) x := fix dbe n := match n with | 0 => x | S n => ν n end.
Notation "x · ν" := (de_bruijn_ext ν x) (at level 2, format "x · ν", right associativity).
Notation "ν ⭳" := (fun n => ν (S n)) (at level 2, format "ν ⭳", no associativity).
Fact de_bruijn_ext_proj X (ν : nat -> X) x n : (x·ν)⭳ n = ν n.
Proof.
reflexivity.
Fact de_bruijn_proj_ext X (ν : nat -> X) n : (ν 0)·(ν⭳) n = ν n.
Proof.
destruct n; reflexivity.
Notation "x '≋' y" := (prod (x->y) (y->x)) (at level 95, no associativity, format "x '≋' y") : type_scope.
Notation "'∀' x .. y , p" := (forall x , .. (forall y , p) ..) (at level 200, x binder, y binder, right associativity, format "'[' '∀' x .. y , '/ ' p ']'", only printing) : type_scope.
Notation "'∃' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity, format "'[' '∃' x .. y , '/ ' p ']'", only printing) : type_scope.
Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..)) (at level 200, x binder, y binder, right associativity, format "'[' '∑' x .. y , '/ ' p ']'", only printing) : type_scope.
Notation "'∑' x .. y ( z : T ) , p" := (sigT (fun x => .. (sigT (fun y => sig (fun z : T => p))) ..)) (at level 200, x binder, y binder, right associativity, format "'[' '∑' x .. y ( z : T ) , '/ ' p ']'", only printing) : type_scope.
Notation "'∑' z : T , p" := (sig (fun z : T => p)) (at level 200, right associativity, format "'[' '∑' z : T , '/ ' p ']'", only printing) : type_scope.
Reserved Notation "⇡ sig" (at level 1, format "⇡ sig").
Reserved Notation "t '⟬' σ '⟭'" (at level 1, format "t ⟬ σ ⟭").
Reserved Notation "'⟦' t '⟧'" (at level 1, format "⟦ t ⟧").
Reserved Notation "f '⦃' σ '⦄'" (at level 1, format "f ⦃ σ ⦄").
Reserved Notation "'⟪' f '⟫'" (at level 1, format "⟪ f ⟫").
Reserved Notation "⌞ x ⌟" (at level 1, format "⌞ x ⌟").
Reserved Notation "↓ x" (at level 1, format "↓ x").
Reserved Notation "x †" (at level 1, format "x †").
Reserved Notation "x ∙ y" (at level 2, right associativity, format "x ∙ y").
Reserved Notation "x ⪧ y" (at level 2, right associativity, format "x ⪧ y").
Reserved Notation "x → y" (at level 2, right associativity, format "x → y").
Reserved Notation "⟬ s , t ⟭" (at level 1, format "⟬ s , t ⟭").
Reserved Notation "x ∪ y" (at level 52, left associativity).
Reserved Notation "x ∈ y" (at level 59, no associativity).
Reserved Notation "x ∉ y" (at level 70, no associativity).
Reserved Notation "x ≈ y" (at level 59, no associativity).
Reserved Notation "x ≉ y" (at level 59, no associativity).
Reserved Notation "x ⊆ y" (at level 59, no associativity).
Reserved Notation "x ≾ y" (at level 70, no associativity).

Fact de_bruijn_proj_ext X (ν : nat -> X) n : (ν 0)·(ν⭳) n = ν n.
Proof.
Admitted.

Fact de_bruijn_ext_proj X (ν : nat -> X) x n : (x·ν)⭳ n = ν n.
Proof.
reflexivity.
