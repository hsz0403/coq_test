Require Import Equations.Equations Equations.Prop.DepElim Arith Undecidability.Shared.Libs.PSL.Numbers List Setoid.
From Undecidability.Synthetic Require Export DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability.FOLP Require Export FullSyntax.
From Undecidability.Shared Require Import ListAutomation.
Require Export Lia.
Import ListAutomationNotations.
Notation "phi --> psi" := (Impl phi psi) (right associativity, at level 55).
Notation "phi ∧ psi" := (Conj phi psi) (right associativity, at level 55).
Notation "phi ∨ psi" := (Disj phi psi) (right associativity, at level 55).
Notation "∀ phi" := (All phi) (at level 56, right associativity).
Notation "∃ phi" := (Ex phi) (at level 56, right associativity).
Notation "⊥" := (Fal).
Notation "¬ phi" := (phi --> ⊥) (at level 20).
Notation vector := Vector.t.
Import Vector.
Arguments nil {A}.
Arguments cons {A} _ {n}.
Derive Signature for vector.
Ltac capply H := eapply H; try eassumption.
Ltac comp := repeat (progress (cbn in *; autounfold in *; asimpl in *)).
Hint Unfold idsRen : core.
Ltac resolve_existT := match goal with | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => rewrite (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H2) in * | _ => idtac end.
Ltac inv H := inversion H; subst; repeat (progress resolve_existT).
Section FullFOL.
Context {Sigma : Signature}.
Definition form_shift n := var_term (S n).
Notation "↑" := form_shift.
Inductive sf : form -> form -> Prop := | SImplL phi psi : sf phi (phi --> psi) | SImplR phi psi : sf psi (phi --> psi) (* | SEq s t s' t' : sf (Pr s' t') (Eq s t) *) | SDisjL phi psi : sf phi (phi ∨ psi) | SDisjR phi psi : sf psi (phi ∨ psi) | SConjL phi psi : sf phi (phi ∧ psi) | SConjR phi psi : sf psi (phi ∧ psi) | SAll phi t : sf (phi [t .: ids]) (∀ phi) | SEx phi t : sf (phi [t .: ids]) (∃ phi).
Fixpoint size (phi : form ) := match phi with | Pred _ _ => 0 | Fal => 0 | Impl phi psi | Conj phi psi | Disj phi psi => S (size phi + size psi) | All phi | Ex phi => S (size phi) end.
Inductive Forall (A : Type) (P : A -> Type) : forall n, vector A n -> Type := | Forall_nil : Forall P (@Vector.nil A) | Forall_cons : forall n (x : A) (l : vector A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).
Inductive vec_in (A : Type) (a : A) : forall n, vector A n -> Type := | vec_inB n (v : vector A n) : vec_in a (cons a v) | vec_inS a' n (v :vector A n) : vec_in a v -> vec_in a (cons a' v).
Hint Constructors vec_in : core.
Inductive unused_term (n : nat) : term -> Prop := | uft_var m : n <> m -> unused_term n (var_term m) | uft_Func F v : (forall t, vec_in t v -> unused_term n t) -> unused_term n (Func F v).
Inductive unused (n : nat) : form -> Prop := | uf_Fal : unused n Fal | uf_Pred P v : (forall t, vec_in t v -> unused_term n t) -> unused n (Pred P v) | uf_I phi psi : unused n phi -> unused n psi -> unused n (Impl phi psi) | uf_A phi psi : unused n phi -> unused n psi -> unused n (Conj phi psi) | uf_O phi psi : unused n phi -> unused n psi -> unused n (Disj phi psi) | uf_All phi : unused (S n) phi -> unused n (All phi) | uf_Ex phi : unused (S n) phi -> unused n (Ex phi).
Definition unused_L n A := forall phi, phi el A -> unused n phi.
Definition closed phi := forall n, unused n phi.
Definition capture n phi := nat_rect _ phi (fun _ => All) n.
Definition close phi := capture (proj1_sig (find_unused phi)) phi.
Fixpoint big_imp A phi := match A with | List.nil => phi | a :: A' => a --> (big_imp A' phi) end.
Definition shift_P P n := match n with | O => False | S n' => P n' end.
Definition theory := form -> Prop.
Definition contains phi (T : theory) := T phi.
Definition contains_L (A : list form) (T : theory) := forall f, f el A -> contains f T.
Definition subset_T (T1 T2 : theory) := forall (phi : form), contains phi T1 -> contains phi T2.
Definition list_T A : theory := fun phi => phi el A.
Infix "⊏" := contains_L (at level 20).
Infix "⊑" := subset_T (at level 20).
Infix "∈" := contains (at level 70).
Hint Unfold contains : core.
Hint Unfold contains_L : core.
Hint Unfold subset_T : core.
Global Instance subset_T_trans : Transitive subset_T.
Proof.
intros T1 T2 T3.
intuition.
Definition extend T (phi : form) := fun psi => T psi \/ psi = phi.
Infix "⋄" := extend (at level 20).
Definition closed_T (T : theory) := forall phi n, contains phi T -> unused n phi.
Section ContainsAutomation.
End ContainsAutomation.
End FullFOL.
Definition tmap {S1 S2 : Signature} (f : @form S1 -> @form S2) (T : @theory S1) : @theory S2 := fun phi => exists psi, T psi /\ f psi = phi.
Hint Constructors vec_in : core.
Infix "⊏" := contains_L (at level 20).
Infix "⊑" := subset_T (at level 20).
Infix "∈" := contains (at level 70).
Infix "⋄" := extend (at level 20).
Hint Resolve contains_nil contains_cons contains_cons2 contains_app : contains_theory.
Hint Resolve contains_extend1 contains_extend2 contains_extend3 : contains_theory.
Ltac use_theory A := exists A; split; [eauto 15 with contains_theory|].
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vector X n).
Proof.
intros v.
refine (dec_vec_in _).
Section EqDec.
Context {Sigma : Signature}.
Hypothesis eq_dec_Funcs : eq_dec Funcs.
Hypothesis eq_dec_Preds : eq_dec Preds.
Global Instance dec_term : eq_dec term.
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
intros t.
induction t using strong_term_ind; intros []...
-
decide (x = n)...
-
decide (F = f)...
destruct (dec_vec_in X t)...
Global Instance dec_form : eq_dec form.
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
intros phi.
induction phi; intros []...
-
decide (P = P0)...
decide (t = t0)...
-
decide (phi1 = f)...
decide (phi2 = f0)...
-
decide (phi1 = f)...
decide (phi2 = f0)...
-
decide (phi1 = f)...
decide (phi2 = f0)...
-
decide (phi = f)...
-
decide (phi = f)...
End EqDec.
Notation "↑" := form_shift.
Notation "A ⟹ phi" := (big_imp A phi) (at level 60).

Lemma var_subst_L A : [phi[var_term] | phi ∈ A] = A.
Proof.
induction A; cbn; trivial.
Admitted.

Lemma sf_acc phi rho : Acc sf (phi [rho]).
Proof.
Admitted.

Lemma sf_well_founded : well_founded sf.
Proof.
intros phi.
pose proof (sf_acc phi ids) as H.
comp.
Admitted.

Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) : (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
Proof.
intros H x.
apply H.
induction (f x).
-
intros y.
lia.
-
intros y.
intros [] % le_lt_or_eq.
+
apply IHn; lia.
+
apply H.
injection H0.
Admitted.

Lemma subst_size rho phi : size (subst_form rho phi) = size phi.
Proof.
Admitted.

Lemma form_ind_subst (P : form -> Prop) : P ⊥ -> (forall p v, P (Pred p v)) -> (forall phi psi, P phi -> P psi -> P (phi --> psi)) -> (forall phi psi, P phi -> P psi -> P (phi ∧ psi)) -> (forall phi psi, P phi -> P psi -> P (phi ∨ psi)) -> (forall phi, (forall t, P phi[t..]) -> P (∀ phi)) -> (forall phi, (forall t, P phi[t..]) -> P (∃ phi)) -> forall phi, P phi.
Proof.
intros H1 H2 H3 H4 H5 H6 H7 phi.
induction phi using (@size_induction _ size).
destruct phi; trivial.
-
apply H3; apply H; cbn; lia.
-
apply H4; apply H; cbn; lia.
-
apply H5; apply H; cbn; lia.
-
apply H6.
intros t.
apply H.
cbn.
unfold subst1.
rewrite subst_size.
lia.
-
apply H7.
intros t.
apply H.
cbn.
unfold subst1.
rewrite subst_size.
Admitted.

Lemma strong_term_ind' (p : term -> Type) : (forall x, p (var_term x)) -> (forall F v, (Forall p v) -> p (Func F v)) -> forall (t : term), p t.
Proof.
intros f1 f2.
fix strong_term_ind' 1.
destruct t as [n|F v].
-
apply f1.
-
apply f2.
induction v.
+
econstructor.
+
econstructor.
now eapply strong_term_ind'.
Admitted.

Lemma strong_term_ind (p : term -> Type) : (forall x, p (var_term x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (Func F v)) -> forall (t : term), p t.
Proof.
intros f1 f2.
eapply strong_term_ind'.
-
apply f1.
-
intros.
apply f2.
intros t.
Admitted.

Lemma vec_unused n (v : vector term n) : (forall t, vec_in t v -> { n | forall m, n <= m -> unused_term m t }) -> { k | forall t, vec_in t v -> forall m, k <= m -> unused_term m t }.
Proof.
intros Hun.
induction v in Hun |-*.
-
exists 0.
intros n H.
inv H.
-
destruct IHv as [k H].
1: eauto.
destruct (Hun h (vec_inB h v)) as [k' H'].
exists (k + k').
intros t H2.
Admitted.

Lemma find_unused_term t : { n | forall m, n <= m -> unused_term m t }.
Proof.
induction t using strong_term_ind.
-
exists (S x).
intros m Hm.
constructor.
lia.
-
destruct (vec_unused X) as [k H].
exists k.
Admitted.

Lemma var_subst phi : phi[var_term] = phi.
Proof.
now asimpl.
