Set Implicit Arguments.
Require Import Morphisms Lia List.
From Undecidability.HOU Require Import calculus.calculus.
Import ListNotations.
Set Default Proof Using "Type".
Section Constants.
Section ConstantsOfTerm.
Context {X: Const}.
Implicit Types (s t: exp X).
Fixpoint consts s := match s with | var x => nil | const c => [c] | lambda s => consts s | app s t => consts s ++ consts t end.
Definition Consts S := (flat_map consts S).
End ConstantsOfTerm.
Section ConstantSubstitution.
Implicit Types (X Y Z : Const).
Fixpoint subst_consts {X Y} (kappa: X -> exp Y) s := match s with | var x => var x | const c => kappa c | lambda s => lambda (subst_consts (kappa >> ren shift) s) | app s t => (subst_consts kappa s) (subst_consts kappa t) end.
Global Instance step_subst_consts X Y: Proper (Logic.eq ++> step ++> step) (@subst_consts X Y).
Proof.
intros ? zeta -> s t H; induction H in zeta |-*; cbn; eauto.
econstructor; subst; unfold beta.
erewrite subst_const_comm with (delta := shift).
f_equal.
fext.
all: intros []; cbn; eauto.
Global Instance steps_subst_consts X Y: Proper (Logic.eq ++> star step ++> star step) (@subst_consts X Y).
Proof.
intros ? zeta -> s t H; induction H in zeta |-*; cbn; eauto; rewrite H; eauto.
Global Instance equiv_subst_consts X Y: Proper (Logic.eq ++> equiv step ++> equiv step) (@subst_consts X Y).
Proof.
intros ? zeta -> s t [v [H1 H2]] % church_rosser; eauto; now rewrite H1, H2.
End ConstantSubstitution.
End Constants.

Lemma Consts_consts s S: s ∈ S -> consts s ⊆ Consts S.
Proof.
Admitted.

Lemma consts_ren delta s: consts (ren delta s) = consts s.
Proof.
Admitted.

Lemma vars_subst_consts x s sigma: x ∈ vars s -> consts (sigma x) ⊆ consts (sigma • s).
Proof.
intros H % vars_varof; induction H in sigma |-*; cbn; intuition.
Admitted.

Lemma consts_subst_in x sigma s: x ∈ consts (sigma • s) -> x ∈ consts s \/ exists y, y ∈ vars s /\ x ∈ consts (sigma y).
Proof.
induction s in sigma |-*.
-
right; exists f; intuition.
-
cbn; intuition.
-
intros H % IHs; cbn -[vars]; intuition.
destruct H0 as [[]]; cbn -[vars] in *; intuition.
right.
exists n.
intuition.
unfold funcomp in H1; now rewrite consts_ren in H1.
-
cbn; simplify; intuition.
+
specialize (IHs1 _ H0); intuition.
destruct H as [y]; right; exists y; intuition.
+
specialize (IHs2 _ H0); intuition.
Admitted.

Lemma consts_subset_step s t: s > t -> consts t ⊆ consts s.
Proof.
induction 1; cbn; intuition.
subst.
unfold beta.
intros x ? % consts_subst_in; simplify; intuition.
Admitted.

Lemma consts_subset_steps s t: s >* t -> consts t ⊆ consts s.
Proof.
Admitted.

Lemma consts_subst_vars sigma s: consts (sigma • s) ⊆ consts s ++ Consts (map sigma (vars s)).
Proof.
intros x [|[y]] % consts_subst_in; simplify; intuition.
Admitted.

Lemma consts_Lam k s: consts (Lambda k s) === consts s.
Proof.
Admitted.

Lemma consts_AppL S t: consts (AppL S t) === Consts S ++ consts t.
Proof.
induction S; cbn; intuition.
Admitted.

Lemma consts_AppR s T: consts (AppR s T) === consts s ++ Consts T.
Proof.
induction T; cbn; intuition.
rewrite IHT.
intuition.
Admitted.

Lemma ren_subst_consts_commute X Y (zeta: X -> exp Y) delta s: subst_consts (zeta >> ren delta) (ren delta s) = ren delta (subst_consts zeta s).
Proof.
induction s in delta, zeta |-*; cbn; eauto.
-
f_equal.
rewrite <-IHs.
f_equal.
asimpl.
reflexivity.
-
Admitted.

Lemma Consts_montone S T: S ⊆ T -> Consts S ⊆ Consts T.
Proof.
unfold Consts; eauto using flat_map_incl.
