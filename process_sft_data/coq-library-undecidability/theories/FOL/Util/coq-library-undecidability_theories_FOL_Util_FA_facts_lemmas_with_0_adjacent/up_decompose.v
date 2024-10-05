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

Lemma up_decompose sigma phi : phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
Proof.
rewrite subst_comp.
apply subst_ext.
intros [].
-
reflexivity.
-
apply subst_term_shift.
