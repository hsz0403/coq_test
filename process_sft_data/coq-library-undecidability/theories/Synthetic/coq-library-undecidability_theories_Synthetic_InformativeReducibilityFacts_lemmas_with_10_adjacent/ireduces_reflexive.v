From Undecidability.Synthetic Require Import InformativeDefinitions DecidabilityFacts.
Set Implicit Arguments.
Section Properties.
Variables (X : Type) (P : X -> Prop) (Y : Type) (Q : Y -> Prop) (Z : Type) (R : Z -> Prop).
Fact ireduces_reflexive : P ⪯ᵢ P.
Proof.
exists (fun x => x); red; tauto.
Fact ireduces_transitive : P ⪯ᵢ Q -> Q ⪯ᵢ R -> P ⪯ᵢ R.
Proof.
unfold inf_reduces, reduction.
intros (f & Hf) (g & Hg).
exists (fun x => g (f x)).
intro; rewrite Hf, Hg; tauto.
Fact ireduces_reduces : P ⪯ᵢ Q -> P ⪯ Q.
Proof.
intros (f & ?); exists f; auto.
Fact reduces_ireduces : P ⪯ Q -> inhabited (P ⪯ᵢ Q).
Proof.
intros (f & ?); exists; exists f; auto.
Fact reduces_ireduces_iff : P ⪯ Q <-> inhabited (P ⪯ᵢ Q).
Proof.
split.
+
apply reduces_ireduces.
+
intros []; apply ireduces_reduces; auto.
Fact ireduces_dependent : (P ⪯ᵢ Q -> forall x, { y | P x <-> Q y }) * ((forall x, { y | P x <-> Q y }) -> P ⪯ᵢ Q).
Proof.
unfold inf_reduces, reduction.
split.
+
intros (f & Hf).
intros x; exists (f x); auto.
+
intros f.
exists (fun x => proj1_sig (f x)).
intros; apply (proj2_sig (f x)).
End Properties.

Fact ireduces_transitive : P ⪯ᵢ Q -> Q ⪯ᵢ R -> P ⪯ᵢ R.
Proof.
unfold inf_reduces, reduction.
intros (f & Hf) (g & Hg).
exists (fun x => g (f x)).
Admitted.

Fact ireduces_reduces : P ⪯ᵢ Q -> P ⪯ Q.
Proof.
Admitted.

Fact reduces_ireduces : P ⪯ Q -> inhabited (P ⪯ᵢ Q).
Proof.
Admitted.

Fact reduces_ireduces_iff : P ⪯ Q <-> inhabited (P ⪯ᵢ Q).
Proof.
split.
+
apply reduces_ireduces.
+
Admitted.

Fact ireduces_dependent : (P ⪯ᵢ Q -> forall x, { y | P x <-> Q y }) * ((forall x, { y | P x <-> Q y }) -> P ⪯ᵢ Q).
Proof.
unfold inf_reduces, reduction.
split.
+
intros (f & Hf).
intros x; exists (f x); auto.
+
intros f.
exists (fun x => proj1_sig (f x)).
Admitted.

Fact ireduces_reflexive : P ⪯ᵢ P.
Proof.
exists (fun x => x); red; tauto.
