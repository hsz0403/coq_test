Set Implicit Arguments.
Require Import Morphisms Lia.
From Undecidability.HOU Require Import std.std.
From Undecidability.HOU.calculus Require Import prelim terms syntax semantics confluence typing order.
Set Default Proof Using "Type".
Section SemanticTyping.
Variable (X: Const).
Definition SemType := exp X -> Prop.
Definition active (s: exp X) := match s with lambda s => True | _ => False end.
Definition C (T: SemType) (s: exp X) := exists t, s ▷ t /\ (active t -> T t).
Fixpoint V (A: type) (s: exp X) := match A with | typevar beta => False | A → B => match s with | lambda s => normal s /\ forall t delta, C (V A) t -> C (V B) ((ren delta (lambda s)) t) | _ => False end end.
Definition E A := C (V A).
Definition G Gamma gamma := forall i A, nth Gamma i = Some A -> E A (gamma i).
Definition ren_closed (S: SemType) := forall delta s, S s -> S (ren delta s).
End SemanticTyping.
Section Soundness.
Context {X: Const}.
Implicit Type (s: exp X).
Definition semtyping Gamma s A := forall gamma, G Gamma gamma -> E A (gamma • s).
Notation "Gamma ⊨ s : A" := (semtyping Gamma s A) (at level 80, s at level 99).
End Soundness.

Lemma closure_under_expansion s t A: s >* t -> E A s -> E A t.
Proof.
intros H [v [[H1 H2] H3]].
exists v.
intuition.
split; eauto.
Admitted.

Lemma closure_under_reduction s t A: s >* t -> E A t -> E A s.
Proof.
intros H [v [[H1 H2] H3]].
exists v; intuition.
Admitted.

Lemma ren_closed_C S: ren_closed S -> ren_closed (C S).
Proof.
intros H delta s; unfold C in *; intros (t & [H1 H2] & H3).
exists (ren delta t); split.
split; eauto using ren_steps, normal_ren.
intros H4.
eapply H, H3.
Admitted.

Lemma ren_closed_V A: ren_closed (V A).
Proof.
induction A as [beta | A IHA B IHB].
-
intros ? ? [].
-
intros delta []; cbn in *; eauto; intros [H1 H2].
split; eauto using normal_ren.
intros t delta' H'.
asimpl.
replace (_ • e) with (ren (upRen_exp_exp (delta >> delta')) e)by now asimpl.
Admitted.

Lemma ren_closed_E A: ren_closed (E A).
Proof.
Admitted.

Lemma ren_closed_G Gamma gamma delta: G Gamma gamma -> G Gamma (gamma >> ren delta).
Proof.
intros H x A E.
Admitted.

Lemma E_var x A: E A (var x).
Proof.
exists (var x).
Admitted.

Lemma G_id Gamma: G Gamma var.
Proof.
intros ???.
Admitted.

Lemma G_cons Gamma A s gamma: G Gamma gamma -> E A s -> G (A :: Gamma) (s .: gamma).
Proof.
intros.
intros [|] B H'; cbn in *.
now injection H' as ->.
Admitted.

Lemma G_up Gamma A gamma: G Gamma gamma -> G (A :: Gamma) (up gamma).
Proof.
Admitted.

Lemma E_evaluates s A: E A s -> exists t, s ▷ t.
Proof.
intros (t & H1 & H2); exists t; intuition.
