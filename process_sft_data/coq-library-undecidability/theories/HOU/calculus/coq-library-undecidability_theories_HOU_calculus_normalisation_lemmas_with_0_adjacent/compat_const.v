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

Lemma compat_const c: E (ctype X c) (const c).
Proof.
exists (const c); split; [split|]; cbn; intuition.
