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

Lemma Consts_montone S T: S ⊆ T -> Consts S ⊆ Consts T.
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

Lemma subst_consts_comp X Y Z (zeta: X -> exp Y) (kappa: Y -> exp Z) s: subst_consts kappa (subst_consts zeta s) = subst_consts (zeta >> subst_consts kappa) s.
Proof.
induction s in zeta, kappa |-*; cbn; eauto.
-
f_equal.
rewrite IHs.
f_equal.
fext.
unfold funcomp at 4; unfold funcomp at 4.
intros; rewrite <-ren_subst_consts_commute.
reflexivity.
-
Admitted.

Lemma subst_consts_ident Y zeta s: (forall x: Y, x ∈ consts s -> zeta x = const x) -> subst_consts zeta s = s.
Proof.
intros; induction s in zeta, H |-*; cbn; eauto.
eapply H; cbn; eauto.
rewrite IHs; eauto.
unfold funcomp; now intros x -> % H.
rewrite IHs1, IHs2; eauto.
Admitted.

Lemma subst_const_comm {X Y} (zeta: X -> exp Y) sigma delta s: (forall x, sigma (delta x) = var x) -> subst_consts zeta (sigma • s) = (sigma >> subst_consts zeta) • (subst_consts (zeta >> ren delta) s).
Proof.
induction s in zeta, sigma, delta |-*; intros H; cbn.
-
reflexivity.
-
unfold funcomp; asimpl.
rewrite idSubst_exp; eauto.
intros y; unfold funcomp; cbn.
rewrite H; reflexivity.
-
f_equal.
erewrite IHs with (delta := 0 .: delta >> shift).
2: intros []; cbn; unfold funcomp; eauto; rewrite H; reflexivity.
f_equal; [| now asimpl].
fext; intros []; cbn; eauto.
unfold funcomp at 2.
now rewrite ren_subst_consts_commute.
-
Admitted.

Lemma subst_consts_consts X Y (zeta: X -> exp Y) (s: exp X): consts (subst_consts zeta s) === Consts (map zeta (consts s)).
Proof.
unfold Consts; induction s in zeta |-*; cbn; simplify; intuition.
-
rewrite IHs.
unfold funcomp; rewrite <-map_map, !flat_map_concat_map, map_map.
erewrite map_ext with (g := consts); intuition.
now rewrite consts_ren.
-
rewrite IHs1, IHs2, !flat_map_concat_map; simplify.
Admitted.

Lemma consts_in_subst_consts X Y (kappa: X -> exp Y) c s: c ∈ consts (subst_consts kappa s) -> exists d, d ∈ consts s /\ c ∈ consts (kappa d).
Proof.
rewrite subst_consts_consts.
unfold Consts; rewrite in_flat_map; intros [e []]; mapinj.
Admitted.

Lemma subst_consts_up Y Z (zeta: Y -> exp Z) (sigma: fin -> exp Y): up (sigma >> subst_consts zeta) = up sigma >> subst_consts (zeta >> ren shift).
Proof.
fext; intros []; cbn; eauto.
unfold funcomp at 1 2.
Admitted.

Lemma subst_const_comm_id Y zeta sigma (s: exp Y): subst_consts zeta s = s -> (sigma >> subst_consts zeta) • s = subst_consts zeta (sigma • s).
Proof.
induction s in zeta, sigma |-*; cbn; eauto.
-
injection 1 as H.
f_equal.
rewrite <-IHs; eauto.
now rewrite subst_consts_up.
-
injection 1 as H.
Admitted.

Lemma consts_Lam k s: consts (Lambda k s) === consts s.
Proof.
induction k; cbn; intuition.
