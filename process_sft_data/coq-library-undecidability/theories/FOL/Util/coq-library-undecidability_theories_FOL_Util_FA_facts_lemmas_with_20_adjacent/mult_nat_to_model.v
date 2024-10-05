From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction.
Require Import Undecidability.FOL.PA.
Require Import Lia List Vector.
Import Vector.VectorNotations.
Section ND.
Variable p : peirce.
Fixpoint iter {X: Type} f n (x : X) := match n with 0 => x | S m => f (iter f m x) end.
Fact iter_switch {X} f n x : f (@iter X f n x) = iter f n (f x).
Proof.
induction n; cbn; now try rewrite IHn.
Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.
Definition forall_times n (phi : form) := iter (fun psi => ∀ psi) n phi.
End ND.
Section SEM.
Context {D : Type}.
Context {I : interp D}.
Fact subst_exist_sat2 N : forall rho phi, rho ⊨ (exist_times N phi) -> (exists sigma, sigma ⊨ phi).
Proof.
induction N.
-
eauto.
-
intros rho phi [? H].
now apply IHN in H.
End SEM.
Section FA_prv.
Variable p : peirce.
Variable Gamma : list form.
Variable G : incl FAeq Gamma.
Fixpoint join {X n} (v : t X n) (rho : nat -> X) := match v with | Vector.nil _ => rho | Vector.cons _ x n w => join w (x.:rho) end.
Local Notation "v '∗' rho" := (join v rho) (at level 20).
Arguments Weak {_ _ _ _}, _.
Fixpoint num n := match n with O => zero | S x => σ (num x) end.
End FA_prv.
Notation "x 'i=' y" := (i_atom (P:=Eq) [x ; y]) (at level 30) : PA_Notation.
Notation "'iO'" := (i_func (f:=Zero) []) (at level 2) : PA_Notation.
Notation "'iσ' d" := (i_func (f:=Succ) [d]) (at level 37) : PA_Notation.
Notation "x 'i⊕' y" := (i_func (f:=Plus) [x ; y]) (at level 39) : PA_Notation.
Notation "x 'i⊗' y" := (i_func (f:=Mult) [x ; y]) (at level 38) : PA_Notation.
Section FA_models.
Variable D : Type.
Variable I : interp D.
Hypothesis ext_model : extensional I.
Hypothesis FA_model : forall ax rho, List.In ax FA -> rho ⊨ ax.
Fixpoint iμ k := match k with | O => iO | S n => iσ (iμ n) end.
Fact eval_num sigma n : eval sigma (num n) = iμ n.
Proof.
induction n.
-
reflexivity.
-
cbn.
now rewrite IHn.
End FA_models.
Arguments iμ {_ _} _.
Section StdModel.
Definition interp_nat : interp nat.
Proof.
split.
-
destruct f; intros v.
+
exact 0.
+
exact (S (Vector.hd v) ).
+
exact (Vector.hd v + Vector.hd (Vector.tl v) ).
+
exact (Vector.hd v * Vector.hd (Vector.tl v) ).
-
destruct P.
intros v.
exact (Vector.hd v = Vector.hd (Vector.tl v) ).
Defined.
Fact nat_extensional : extensional interp_nat.
Proof.
now intros x y.
Fact nat_eval_num (sigma : env nat) n : @eval _ _ _ interp_nat sigma (num n) = n.
Proof.
induction n.
-
reflexivity.
-
cbn.
now rewrite IHn.
Fact nat_induction phi : forall rho, sat interp_nat rho (ax_induction phi).
Proof.
intros rho H0 IH d.
induction d; cbn in *.
rewrite <-sat_single in H0.
apply H0.
apply IH in IHd.
rewrite sat_comp in IHd.
revert IHd.
apply sat_ext.
intros []; reflexivity.
Fact nat_is_PAeq_model : forall ax rho, PAeq ax -> sat interp_nat rho ax.
Proof.
intros rho psi [].
now apply nat_is_FA_model.
all: cbn; try congruence.
apply nat_induction.
Fact nat_is_PA_model : forall ax rho, PA ax -> sat interp_nat rho ax.
Proof.
intros rho psi [].
repeat (destruct H as [<- | H]; auto).
all: cbn; try congruence.
apply nat_induction.
End StdModel.

Lemma subst_exist_sat rho phi N : rho ⊨ phi -> bounded N phi -> forall rho, rho ⊨ (exist_times N phi).
Proof.
induction N in phi, rho |-*; intros.
-
cbn.
eapply sat_closed; eassumption.
-
cbn -[sat].
rewrite iter_switch.
apply (IHN (S >> rho)).
exists (rho 0).
eapply sat_ext.
2: apply H.
now intros [].
Admitted.

Fact subst_exist_sat2 N : forall rho phi, rho ⊨ (exist_times N phi) -> (exists sigma, sigma ⊨ phi).
Proof.
induction N.
-
eauto.
-
intros rho phi [? H].
Admitted.

Lemma reflexivity t : Gamma ⊢ (t == t).
Proof.
apply (Weak FAeq).
pose (sigma := [t] ∗ var ).
change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $0)[sigma]).
eapply (@subst_forall_prv _ _ 1).
apply Ctx.
all : firstorder.
constructor.
Admitted.

Lemma symmetry x y : Gamma ⊢ (x == y) -> Gamma ⊢ (y == x).
Proof.
apply IE.
apply (Weak FAeq).
pose (sigma := [x ; y] ∗ var ).
change (FAeq ⊢ _) with (FAeq ⊢ ($1 == $0 ~> $0 == $1)[sigma]).
apply (@subst_forall_prv _ _ 2).
apply Ctx.
all : firstorder.
Admitted.

Lemma transitivity x y z : Gamma ⊢ (x == y) -> Gamma ⊢ (y == z) -> Gamma ⊢ (x == z).
Proof.
intros H.
apply IE.
revert H; apply IE.
apply Weak with FAeq.
pose (sigma := [x ; y ; z] ∗ var).
change (FAeq ⊢ _) with (FAeq ⊢ ($2 == $1 ~> $1 == $0 ~> $2 == $0)[sigma]).
apply (@subst_forall_prv _ _ 3).
apply Ctx.
all : try firstorder.
Admitted.

Lemma eq_succ x y : Gamma ⊢ (x == y) -> Gamma ⊢ (σ x == σ y).
Proof.
apply IE.
apply Weak with FAeq.
pose (sigma := [y ; x] ∗ var ).
change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> σ $0 == σ $1)[sigma]).
apply (@subst_forall_prv _ _ 2).
apply Ctx.
all : firstorder.
Admitted.

Lemma eq_add {x1 y1 x2 y2} : Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊕ y1 == x2 ⊕ y2).
Proof.
intros H; apply IE.
revert H; apply IE.
apply Weak with FAeq.
pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊕ $2 == $1 ⊕ $3)[sigma]).
apply (@subst_forall_prv _ _ 4).
apply Ctx.
all: firstorder.
Admitted.

Lemma eq_mult {x1 y1 x2 y2} : Gamma ⊢ (x1 == x2) -> Gamma ⊢ (y1 == y2) -> Gamma ⊢ (x1 ⊗ y1 == x2 ⊗ y2).
Proof.
intros H; apply IE.
revert H; apply IE.
apply Weak with FAeq.
pose (sigma := [y2 ; y1 ; x2 ; x1] ∗ var).
change (FAeq ⊢ _) with (FAeq ⊢ ($0 == $1 ~> $2 == $3 ~> $0 ⊗ $2 == $1 ⊗ $3)[sigma]).
apply (@subst_forall_prv _ _ 4).
apply Ctx.
all: firstorder.
Admitted.

Lemma Add_rec x y : Gamma ⊢ ( (σ x) ⊕ y == σ (x ⊕ y) ).
Proof.
apply Weak with FAeq.
pose (sigma := [y ; x] ∗ var).
change (FAeq ⊢ _) with (FAeq ⊢ (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[sigma]).
apply (@subst_forall_prv _ _ 2).
apply Ctx.
all : firstorder.
Admitted.

Lemma num_add_homomorphism x y : Gamma ⊢ ( num x ⊕ num y == num (x + y) ).
Proof.
induction x; cbn.
-
apply (@AllE _ _ _ _ _ _ (zero ⊕ $0 == $0) ).
apply Weak with FAeq.
apply Ctx;firstorder.
assumption.
-
eapply transitivity.
apply Add_rec.
Admitted.

Lemma Mult_rec x y : Gamma ⊢ ( (σ x) ⊗ y == y ⊕ (x ⊗ y) ).
Proof.
apply Weak with FAeq.
pose (sigma := [x ; y] ∗ var).
change (FAeq ⊢ _) with (FAeq ⊢ ((σ $1) ⊗ $0 == $0 ⊕ ($1 ⊗ $0))[sigma]).
eapply (@subst_forall_prv _ _ 2).
apply Ctx.
all : firstorder.
Admitted.

Lemma num_mult_homomorphism (x y : nat) : Gamma ⊢ ( num x ⊗ num y == num (x * y) ).
Proof.
induction x; cbn.
-
apply (@AllE _ _ _ _ _ _ (zero ⊗ $0 == zero)).
apply Weak with FAeq.
apply Ctx; firstorder.
assumption.
-
eapply transitivity.
apply Mult_rec.
eapply transitivity.
2: apply num_add_homomorphism.
apply eq_add.
apply reflexivity.
Admitted.

Fact eval_num sigma n : eval sigma (num n) = iμ n.
Proof.
induction n.
-
reflexivity.
-
cbn.
Admitted.

Lemma add_zero : forall d : D, iO i⊕ d = d.
Proof.
intros d.
assert (List.In ax_add_zero FA) as H by firstorder.
specialize (FA_model ax_add_zero (d.:(fun _ => iO)) H).
cbn in FA_model.
Admitted.

Lemma add_rec : forall n d : D, iσ n i⊕ d = iσ (n i⊕ d).
Proof.
intros n d.
assert (List.In ax_add_rec FA) as H by firstorder.
specialize (FA_model ax_add_rec (d.:(fun _ => iO)) H).
cbn in FA_model.
Admitted.

Lemma mult_zero : forall d : D, iO i⊗ d = iO.
Proof.
intros d.
assert (List.In ax_mult_zero FA) as H by firstorder.
specialize (FA_model ax_mult_zero (d.:(fun _ => iO)) H).
cbn in FA_model.
Admitted.

Lemma mult_rec : forall n d : D, iσ d i⊗ n = n i⊕ d i⊗ n.
Proof.
intros n d.
assert (List.In ax_mult_rec FA) as H by firstorder.
specialize (FA_model ax_mult_rec (d.:(fun _ => iO)) H).
cbn in FA_model.
Admitted.

Corollary add_hom x y : iμ (x + y) = iμ x i⊕ iμ y.
Proof.
induction x.
-
now rewrite add_zero.
-
change (iσ iμ (x + y) = iσ iμ x i⊕ iμ y).
Admitted.

Corollary add_nat_to_model : forall x y z, x + y = z -> (iμ x i⊕ iμ y = iμ z).
Proof.
intros x y z H.
Admitted.

Corollary mult_hom x y : iμ (x * y) = iμ x i⊗ iμ y.
Proof.
induction x.
-
now rewrite mult_zero.
-
change (iμ (y + x * y) = (iσ iμ x) i⊗ iμ y ).
Admitted.

Definition interp_nat : interp nat.
Proof.
split.
-
destruct f; intros v.
+
exact 0.
+
exact (S (Vector.hd v) ).
+
exact (Vector.hd v + Vector.hd (Vector.tl v) ).
+
exact (Vector.hd v * Vector.hd (Vector.tl v) ).
-
destruct P.
intros v.
Admitted.

Fact nat_extensional : extensional interp_nat.
Proof.
Admitted.

Lemma nat_is_FA_model : forall rho phi, List.In phi FAeq -> sat interp_nat rho phi.
Proof.
intros rho phi.
intros H.
repeat (destruct H as [<- | H]; auto).
Admitted.

Fact nat_eval_num (sigma : env nat) n : @eval _ _ _ interp_nat sigma (num n) = n.
Proof.
induction n.
-
reflexivity.
-
cbn.
Admitted.

Fact nat_induction phi : forall rho, sat interp_nat rho (ax_induction phi).
Proof.
intros rho H0 IH d.
induction d; cbn in *.
rewrite <-sat_single in H0.
apply H0.
apply IH in IHd.
rewrite sat_comp in IHd.
revert IHd.
apply sat_ext.
Admitted.

Fact nat_is_PAeq_model : forall ax rho, PAeq ax -> sat interp_nat rho ax.
Proof.
intros rho psi [].
now apply nat_is_FA_model.
all: cbn; try congruence.
Admitted.

Fact nat_is_PA_model : forall ax rho, PA ax -> sat interp_nat rho ax.
Proof.
intros rho psi [].
repeat (destruct H as [<- | H]; auto).
all: cbn; try congruence.
Admitted.

Corollary mult_nat_to_model : forall z x y, x * y = z -> (iμ x i⊗ iμ y = iμ z).
Proof.
intros x y z H.
now rewrite <- mult_hom, H.
