From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts MoreEnumerabilityFacts.
From Undecidability.Shared Require Import ListAutomation.
Require Import List.
Import ListNotations ListAutomationNotations.
Set Implicit Arguments.
Section Properties.
Variables (X : Type) (P : X -> Prop) (Y : Type) (Q : Y -> Prop) (Z : Type) (R : Z -> Prop).
Fact reduces_reflexive : P ⪯ P.
Proof.
exists (fun x => x); red; tauto.
Fact reduces_transitive : P ⪯ Q -> Q ⪯ R -> P ⪯ R.
Proof.
unfold reduces, reduction.
intros (f & Hf) (g & Hg).
exists (fun x => g (f x)).
intro; rewrite Hf, Hg; tauto.
Fact reduces_dependent : P ⪯ Q <-> inhabited (forall x, { y | P x <-> Q y }).
Proof.
constructor.
-
intros [f Hf].
constructor.
intros x.
now exists (f x).
-
intros [f].
exists (fun x => proj1_sig (f x)).
intros x.
exact (proj2_sig (f x)).
End Properties.
Module ReductionChainNotations.
Ltac redchain2Prop_rec xs := lazymatch xs with | pair ?x (pair ?y ?xs) => let z := redchain2Prop_rec (pair y xs) in constr:(x ⪯ y /\ z) | pair ?x ?y => constr:(x ⪯ y) end.
Ltac redchain2Prop xs := let z := redchain2Prop_rec xs in exact z.
Declare Scope reduction_chain.
Delimit Scope reduction_chain with redchain_scope.
Notation "x '⪯ₘ' y" := (pair x y) (at level 80, right associativity, only parsing) : reduction_chain.
Notation "'⎩' xs '⎭'" := (ltac:(redchain2Prop (xs % redchain_scope))) (only parsing).
End ReductionChainNotations.
Section enum_red.
Variables (X Y : Type) (p : X -> Prop) (q : Y -> Prop).
Variables (f : X -> Y) (Hf : forall x, p x <-> q (f x)).
Variables (Lq : _) (qe : list_enumerator Lq q).
Variables (x0 : X).
Variables (d : eq_dec Y).
Local Fixpoint L L' n := match n with | 0 => [] | S n => L L' n ++ [ x | x ∈ cumul L' n , In (f x) (cumul Lq n) ] end.
Local Lemma enum_red L' : list_enumerator__T L' X -> list_enumerator (L L') p.
Proof.
intros HL'.
split.
+
intros H.
eapply Hf in H.
eapply (cumul_spec qe) in H as [m1].
destruct (cumul_spec__T HL' x) as [m2 ?].
exists (1 + m1 + m2).
cbn.
in_app 2.
in_collect x.
eapply cum_ge'; eauto; try lia.
eapply cum_ge'; eauto; try lia.
+
intros [m H].
induction m.
*
inversion H.
*
cbn in H.
inv_collect.
eapply Hf.
eauto.
End enum_red.

Fact reduces_reflexive : P ⪯ P.
Proof.
Admitted.

Fact reduces_transitive : P ⪯ Q -> Q ⪯ R -> P ⪯ R.
Proof.
unfold reduces, reduction.
intros (f & Hf) (g & Hg).
exists (fun x => g (f x)).
Admitted.

Lemma dec_red X (p : X -> Prop) Y (q : Y -> Prop) : p ⪯ q -> decidable q -> decidable p.
Proof.
unfold decidable, decider, reduces, reduction, reflects.
intros [f] [d].
exists (fun x => d (f x)).
intros x.
rewrite H.
Admitted.

Lemma red_comp X (p : X -> Prop) Y (q : Y -> Prop) : p ⪯ q -> (fun x => ~ p x) ⪯ (fun y => ~ q y).
Proof.
intros [f].
exists f.
intros x.
red in H.
Admitted.

Lemma enumerable_red X Y (p : X -> Prop) (q : Y -> Prop) : p ⪯ q -> enumerable__T X -> discrete Y -> enumerable q -> enumerable p.
Proof.
intros [f] [] % enum_enumT [] % discrete_iff [L] % enumerable_enum.
eapply list_enumerable_enumerable.
eexists.
Admitted.

Theorem not_decidable X Y (p : X -> Prop) (q : Y -> Prop) : p ⪯ q -> enumerable__T X -> ~ enumerable (complement p) -> ~ decidable q /\ ~ decidable (complement q).
Proof.
intros.
split; intros ?.
-
eapply H1.
eapply dec_red in H2; eauto.
eapply dec_compl in H2.
eapply dec_count_enum; eauto.
-
eapply H1.
eapply dec_red in H2; eauto.
eapply dec_count_enum; eauto.
Admitted.

Theorem not_coenumerable X Y (p : X -> Prop) (q : Y -> Prop) : p ⪯ q -> enumerable__T X -> ~ enumerable (complement p) -> discrete Y -> ~ enumerable (complement q).
Proof.
intros.
intros ?.
eapply H1.
eapply enumerable_red in H3; eauto.
Admitted.

Fact reduces_dependent : P ⪯ Q <-> inhabited (forall x, { y | P x <-> Q y }).
Proof.
constructor.
-
intros [f Hf].
constructor.
intros x.
now exists (f x).
-
intros [f].
exists (fun x => proj1_sig (f x)).
intros x.
exact (proj2_sig (f x)).
