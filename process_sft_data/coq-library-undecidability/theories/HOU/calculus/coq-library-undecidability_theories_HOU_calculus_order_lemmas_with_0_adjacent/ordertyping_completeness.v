Set Implicit Arguments.
Require Import List Arith Lia.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics typing.
Set Default Proof Using "Type".
Section OrderTyping.
Context {X: Const}.
Definition ctx := list type.
Implicit Types (s t: exp X) (n m: nat) (Gamma Delta Sigma: ctx) (x y: fin) (c d: X) (A B: type) (sigma tau: fin -> exp X) (delta xi: fin -> fin).
Section Order.
Fixpoint ord A := match A with | typevar beta => 1 | A → B => max (S (ord A)) (ord B) end.
Fixpoint ord' Gamma := match Gamma with | nil => 0 | A :: Gamma => max (ord A) (ord' Gamma) end.
End Order.
Hint Resolve ord'_cons : core.
Reserved Notation "Gamma '⊢(' n ')' s ':' A" (at level 80, s at level 99).
Inductive ordertyping n Gamma: exp X -> type -> Prop := | ordertypingVar x A: ord A <= n -> nth Gamma x = Some A -> Gamma ⊢(n) (var x) : A | ordertypingConst c: ord (ctype X c) <= S n -> Gamma ⊢(n) (const c) : ctype X c | ordertypingLam s A B: A :: Gamma ⊢(n) s : B -> Gamma ⊢(n) lambda s : A → B | ordertypingApp s t A B: Gamma ⊢(n) s : A → B -> Gamma ⊢(n) t : A -> Gamma ⊢(n) s t : B where "Gamma '⊢(' n ')' s ':' A" := (ordertyping n Gamma s A).
Hint Constructors ordertyping : core.
Hint Resolve ordertyping_monotone : core.
Definition ordertypingSubst n Delta sigma Gamma := forall i A, nth Gamma i = Some A -> Delta ⊢(n) sigma i : A.
Notation "Delta ⊩( n ) sigma : Gamma" := (ordertypingSubst n Delta sigma Gamma) (at level 80, sigma at level 99).
Section PreservationOrdertyping.
End PreservationOrdertyping.
End OrderTyping.
Notation "Gamma '⊢(' n ')' s ':' A" := (ordertyping n Gamma s A) (at level 80, s at level 99).
Notation "Delta ⊩( n ) sigma : Gamma" := (ordertypingSubst n Delta sigma Gamma) (at level 80, sigma at level 99).
Hint Constructors ordertyping : core.
Hint Rewrite ord_arr ord'_app ord'_rev : simplify.
Hint Resolve ord'_cons ord'_in : core.
Hint Resolve vars_ordertyping_nth ordertyping_monotone ordertyping_step ordertyping_soundness : core.
Hint Resolve ordertyping_preservation_under_renaming ordertyping_preservation_under_substitution : core.
Hint Resolve ord_target ord_target' : core.

Lemma ordertyping_completeness Gamma s A: Gamma ⊢ s : A -> exists n, Gamma ⊢(n) s : A.
Proof.
induction 1.
-
exists (ord A); eauto.
-
exists (ord (ctype X c)); eauto.
-
destruct IHtyping as [n]; exists (max (S (ord A)) n).
econstructor; eauto.
-
destruct IHtyping1 as [n], IHtyping2 as [m].
exists (max n m); econstructor; eauto.
