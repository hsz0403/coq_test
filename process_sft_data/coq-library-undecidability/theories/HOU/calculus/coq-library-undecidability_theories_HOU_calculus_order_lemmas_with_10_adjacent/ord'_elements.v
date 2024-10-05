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

Lemma ord_1 A: 1 <= ord A.
Proof.
induction A; cbn [ord]; eauto.
Admitted.

Lemma ord_arr A B: ord (A → B) = max (S (ord A)) (ord B).
Proof.
Admitted.

Lemma ord_arr_one A B: ~ ord (A → B) <= 1.
Proof.
intros H; rewrite ord_arr in H; eapply Nat.max_lub_l in H.
Admitted.

Lemma ord'_app Gamma Gamma': ord' (Gamma ++ Gamma') = max (ord' Gamma) (ord' Gamma').
Proof.
induction Gamma; cbn; eauto.
Admitted.

Lemma ord'_rev L: ord' (rev L) = ord' L.
Proof.
induction L; cbn; rewrite ?ord'_app; eauto.
simplify; cbn; eauto.
rewrite IHL.
simplify.
Admitted.

Lemma ord'_in A Gamma: A ∈ Gamma -> ord A <= ord' Gamma.
Proof.
Admitted.

Lemma ord'_cons n Gamma A: ord A < n -> ord' Gamma <= n -> ord' (A :: Gamma) <= n.
Proof.
Admitted.

Lemma order_head Gamma s A B: Gamma ⊢ s : A -> Gamma ⊢ (head s) : B -> isAtom (head s) -> ord A <= ord B.
Proof.
induction 1; eauto; cbn.
-
intros H1 _; inv H1.
rewrite H in H2; injection H2 as ->; eauto.
-
intros H1; inv H1; eauto.
-
cbn in *; intuition.
-
intros; rewrite <-IHtyping1; eauto.
Admitted.

Lemma ord_target A: ord (target A) <= 1.
Proof.
Admitted.

Lemma ord_target' Gamma: ord' (target' Gamma) <= 1.
Proof.
Admitted.

Lemma ordertyping_step n Gamma s A: Gamma ⊢(n) s : A -> Gamma ⊢(S n) s: A.
Proof.
Admitted.

Lemma ordertyping_monotone m n Gamma s A: m <= n -> Gamma ⊢(m) s : A -> Gamma ⊢(n) s: A.
Proof.
Admitted.

Lemma ordertyping_soundness n Gamma s A: Gamma ⊢(n) s : A -> Gamma ⊢ s : A.
Proof.
Admitted.

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
Admitted.

Lemma vars_ordertyping n x s A Gamma: x ∈ vars s -> Gamma ⊢(n) s : A -> exists B, nth Gamma x = Some B /\ ord B <= n.
Proof.
intros H % vars_varof; induction 1 in x, H |-*; inv H; eauto.
Admitted.

Lemma vars_ordertyping_nth n x s A B Gamma: x ∈ vars s -> Gamma ⊢(n) s : A -> nth Gamma x = Some B -> ord B <= n.
Proof.
intros; edestruct vars_ordertyping; eauto.
Admitted.

Lemma ord'_elements n Gamma: (forall A, A ∈ Gamma -> ord A <= n) <-> ord' Gamma <= n.
Proof.
induction Gamma; cbn; intuition; subst; eauto.
all: simplify in *; intuition.
