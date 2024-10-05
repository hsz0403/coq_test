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

Lemma subst_consts_Lambda Y Z (zeta: Y -> exp Z) k s: subst_consts zeta (Lambda k s) = Lambda k (subst_consts (zeta >> ren (plus k)) s).
Proof.
induction k in zeta |-*; cbn; asimpl; eauto.
f_equal.
rewrite IHk.
f_equal.
f_equal.
asimpl.
fext; intros x; unfold funcomp; f_equal; fext; intros ?.
unfold shift; simplify; f_equal; lia.
