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

Lemma vars_ordertyping_nth n x s A B Gamma: x ∈ vars s -> Gamma ⊢(n) s : A -> nth Gamma x = Some B -> ord B <= n.
Proof.
intros; edestruct vars_ordertyping; eauto.
Admitted.

Lemma ordertypingSubst_monotone n m sigma Delta Gamma: n <= m -> Delta ⊩(n) sigma : Gamma -> Delta ⊩(m) sigma : Gamma.
Proof.
Admitted.

Lemma ordertypingSubst_soundness n Delta (sigma: fin -> exp X) Gamma: Delta ⊩(n) sigma : Gamma -> Delta ⊩ sigma : Gamma.
Proof.
Admitted.

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
Admitted.

Lemma ordertyping_weak_preservation_under_renaming Gamma n s A delta Delta: Gamma ⊢(n) s : A -> (forall x A, nth Gamma x = Some A -> x ∈ vars s -> nth Delta (delta x) = Some A) -> Delta ⊢( n) ren delta s : A.
Proof.
induction s in delta, Gamma, Delta, A |-*; cbn -[vars]; intros; inv H; eauto.
-
econstructor.
eapply IHs; eauto.
intros [] ? ?; cbn -[vars] in *; intuition.
-
Admitted.

Lemma ordertyping_preservation_under_renaming n delta Gamma Delta s A: Gamma ⊢(n) s : A -> Delta ⊫ delta : Gamma -> Delta ⊢(n) ren_exp delta s : A.
Proof.
Admitted.

Lemma ordertyping_weak_preservation_under_substitution n sigma Gamma Delta s A: Gamma ⊢(n) s : A -> (forall i A, i ∈ vars s -> nth Gamma i = Some A -> Delta ⊢(n) sigma i : A) -> Delta ⊢(n) sigma • s : A.
Proof.
induction 1 in sigma, Delta |-*; intros H'; cbn [subst_exp]; subst; eauto.
-
econstructor; eauto; eapply IHordertyping.
intros [|m]; cbn; eauto.
+
intros ? H1; injection 1 as <-; econstructor; cbn; eauto.
eapply vars_ordertyping in H1 as []; eauto.
intuition.
now injection H1 as ->.
+
intros D H1 H2; unfold funcomp.
eapply ordertyping_preservation_under_renaming; eauto.
now intros i.
-
econstructor; [eapply IHordertyping1 | eapply IHordertyping2].
Admitted.

Lemma ordertyping_preservation_under_substitution n sigma Gamma Delta s A: Gamma ⊢(n) s : A -> Delta ⊩(n) sigma : Gamma -> Delta ⊢(n) sigma • s : A.
Proof.
Admitted.

Lemma ordertyping_preservation_under_reduction n s s' Gamma A: s > s' -> Gamma ⊢(n) s : A -> Gamma ⊢(n) s' : A.
Proof.
induction 1 in n, Gamma, A |-*; intros H1; invp @ordertyping; eauto.
inv H3.
eapply ordertyping_weak_preservation_under_substitution; eauto.
intros []; cbn; eauto.
intros ? _; now injection 1 as ->.
intros D H6 H7.
eapply vars_ordertyping in H6 as [B]; eauto.
intuition.
econstructor; intuition.
Admitted.

Lemma ordertyping_preservation_under_steps n (s s': exp X) (Gamma: ctx) A: s >* s' -> Gamma ⊢(n) s : A -> Gamma ⊢(n) s' : A.
Proof.
Admitted.

Lemma weakening_ordertyping_app n Gamma Delta s A: Gamma ⊢(n) s : A -> Gamma ++ Delta ⊢(n) s : A.
Proof.
intros H; replace s with (ren id s) by now asimpl.
eapply ordertyping_preservation_under_renaming; eauto.
intros i B H'; unfold id.
rewrite nth_error_app1; eauto.
eapply nth_error_Some_lt; eauto.
