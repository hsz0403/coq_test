Set Implicit Arguments.
Require Import List Lia.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics.
Set Default Proof Using "Type".
Section Typing.
Context {X: Const}.
Definition ctx := list type.
Implicit Types (s t: exp X) (n m: nat) (Gamma Delta Sigma: ctx) (x y: fin) (c d: X) (A B: type) (sigma tau: fin -> exp X) (delta xi: fin -> fin).
Reserved Notation "Gamma ⊢ s : A" (at level 80, s at level 99).
Inductive typing Gamma : exp X -> type -> Prop := | typingVar i A: nth Gamma i = Some A -> Gamma ⊢ var i : A | typingConst c: Gamma ⊢ const c : ctype X c | typingLam s A B: A :: Gamma ⊢ s : B -> Gamma ⊢ lambda s : A → B | typingApp s t A B: Gamma ⊢ s : A → B -> Gamma ⊢ t : A -> Gamma ⊢ s t : B where "Gamma ⊢ s : A" := (typing Gamma s A).
Hint Constructors typing : core.
Definition typingRen Delta delta Gamma := forall x A, nth Gamma x = Some A -> nth Delta (delta x) = Some A.
Notation "Delta ⊫ delta : Gamma" := (typingRen Delta delta Gamma) (at level 80, delta at level 99).
Definition typingSubst Delta sigma Gamma := forall x A, nth Gamma x = Some A -> Delta ⊢ sigma x : A.
Notation "Delta ⊩ sigma : Gamma" := (typingSubst Delta sigma Gamma) (at level 80, sigma at level 99).
Section Preservation.
End Preservation.
End Typing.
Notation "Gamma ⊢ s : A" := (typing Gamma s A) (at level 80, s at level 99).
Notation "Delta ⊫ delta : Gamma" := (typingRen Delta delta Gamma) (at level 80, delta at level 99).
Notation "Delta ⊩ sigma : Gamma" := (typingSubst Delta sigma Gamma) (at level 80, sigma at level 99).
Hint Constructors typing : core.
Hint Resolve typing_variables : core.
Hint Resolve preservation_under_renaming preservation_under_substitution : core.

Lemma typingSubst_cons Delta sigma s Gamma A: Delta ⊩ sigma : Gamma -> Delta ⊢ s : A -> Delta ⊩ s .: sigma : A :: Gamma.
Proof.
intros ??[|]; cbn; eauto; now intros ? [= ->].
