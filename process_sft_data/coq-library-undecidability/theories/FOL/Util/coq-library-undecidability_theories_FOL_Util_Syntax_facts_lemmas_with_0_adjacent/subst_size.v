From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.
Require Import Coq.Vectors.Vector.
Local Notation vec := t.
From Undecidability Require Export FOL.Util.Syntax.
Require Import Equations.Equations.
Section fix_signature.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type := | Forall_nil : Forall P (@Vector.nil A) | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).
Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type := | vec_inB {n} (v : t A n) : vec_in a (cons A a n v) | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
Hint Constructors vec_in : core.
Fixpoint size {ff : falsity_flag} (phi : form) := match phi with | atom _ _ => 0 | falsity => 0 | bin b phi psi => S (size phi + size psi) | quant q phi => S (size phi) end.
Derive Signature for form.
End fix_signature.
Section Subst.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
End Subst.
Section Bounded.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Inductive bounded_t n : term -> Prop := | bounded_var x : n > x -> bounded_t n $x | bouded_func f v : (forall t, Vector.In t v -> bounded_t n t) -> bounded_t n (func f v).
Inductive bounded : forall {ff}, nat -> form ff -> Prop := | bounded_atom ff n P v : (forall t, Vector.In t v -> bounded_t n t) -> @bounded ff n (atom P v) | bounded_bin binop ff n phi psi : @bounded ff n phi -> @bounded ff n psi -> @bounded ff n (bin binop phi psi) | bounded_quant quantop ff n phi : @bounded ff (S n) phi -> @bounded ff n (quant quantop phi) | bounded_falsity n : @bounded falsity_on n falsity.
Arguments bounded {_} _ _.
Definition bounded_L {ff : falsity_flag} n A := forall phi, phi el A -> bounded n phi.
Derive Signature for In.
End Bounded.
Ltac solve_bounds := repeat constructor; try lia; try inversion X; intros; match goal with | H : Vector.In ?x (@Vector.cons _ ?y _ ?v) |- _ => repeat apply vec_cons_inv in H as [->|H]; try inversion H | H : Vector.In ?x (@Vector.nil _) |- _ => try inversion H | _ => idtac end.
Require Import EqdepFacts.
Ltac resolve_existT := try match goal with | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)] end.
Instance dec_vec X {HX : eq_dec X} n : eq_dec (vec X n).
Proof.
intros v.
refine (dec_vec_in _ _ _ _).
Section EqDec.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Hypothesis eq_dec_Funcs : eq_dec syms.
Hypothesis eq_dec_Preds : eq_dec preds.
Hypothesis eq_dec_binop : eq_dec binop.
Hypothesis eq_dec_quantop : eq_dec quantop.
Global Instance dec_term : eq_dec term.
Proof with subst; try (now left + (right; intros[=]; resolve_existT; congruence)).
intros t.
induction t as [ | ]; intros [|? v']...
-
decide (x = n)...
-
decide (F = f)...
destruct (dec_vec_in _ _ _ X v')...
Instance dec_falsity : eq_dec falsity_flag.
Proof.
intros b b'.
unfold dec.
decide equality.
Global Instance dec_form {ff : falsity_flag} : eq_dec form.
Proof.
intros phi psi.
destruct (dec_form_dep phi psi); rewrite eq_dep_falsity in *; firstorder.
End EqDec.
Section Enumerability.
Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.
Context {ops : operators}.
Variable list_Funcs : nat -> list syms.
Hypothesis enum_Funcs' : list_enumerator__T list_Funcs syms.
Variable list_Preds : nat -> list preds.
Hypothesis enum_Preds' : list_enumerator__T list_Preds preds.
Variable list_binop : nat -> list binop.
Hypothesis enum_binop' : list_enumerator__T list_binop binop.
Variable list_quantop : nat -> list quantop.
Hypothesis enum_quantop' : list_enumerator__T list_quantop quantop.
Fixpoint vecs_from X (A : list X) (n : nat) : list (vec X n) := match n with | 0 => [Vector.nil X] | S n => [ Vector.cons X x _ v | (x, v) ∈ (A × vecs_from X A n) ] end.
Fixpoint L_term n : list term := match n with | 0 => [] | S n => L_term n ++ var n :: concat ([ [ func F v | v ∈ vecs_from _ (L_term n) (ar_syms F) ] | F ∈ L_T n]) end.
Fixpoint L_form {ff : falsity_flag} n : list form := match n with | 0 => match ff with falsity_on => [falsity] | falsity_off => [] end | S n => L_form n ++ concat ([ [ atom P v | v ∈ vecs_from _ (L_term n) (ar_preds P) ] | P ∈ L_T n]) ++ concat ([ [ bin op phi psi | (phi, psi) ∈ (L_form n × L_form n) ] | op ∈ L_T n]) ++ concat ([ [ quant op phi | phi ∈ L_form n ] | op ∈ L_T n]) end.

Lemma subst_size {ff : falsity_flag} rho phi : size (subst_form rho phi) = size phi.
Proof.
revert rho; induction phi; intros rho; cbn; congruence.
