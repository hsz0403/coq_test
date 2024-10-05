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

Lemma ordertypingSubst_complete Delta sigma Gamma: Delta ⊩ sigma : Gamma -> exists n, Delta ⊩(n) sigma : Gamma.
Proof.
induction Gamma as [| A Gamma IH] in sigma |-* .
-
intros _.
exists 0.
intros []?; cbn; discriminate.
-
intros ?.
specialize (IH (shift >> sigma)).
mp IH; [intros ???; eauto|].
specialize (H 0 A); mp H; eauto.
eapply ordertyping_completeness in H.
destruct IH as [n], H as [m].
exists (max n m); intros [|x]B; cbn; [injection 1 as ->|intros].
all: eapply ordertyping_monotone.
2, 4: eauto.
all: eauto.
