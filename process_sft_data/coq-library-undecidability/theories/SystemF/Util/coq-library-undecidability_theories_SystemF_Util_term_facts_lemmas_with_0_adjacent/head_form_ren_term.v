Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition term_norm := (@subst_term_up_term_term_var, @subst_term_up_term_poly_type, @subst_term_up_poly_type_term_var, @subst_term_ren_term).
Inductive head_form : term -> Prop := | head_form_var {x} : head_form (var x) | head_form_app {P Q} : head_form P -> normal_form Q -> head_form (app P Q) | head_form_ty_app {P t} : head_form P -> head_form (ty_app P t) with normal_form : term -> Prop := | normal_form_head_form {P} : head_form P -> normal_form P | normal_form_abs {s P} : normal_form P -> normal_form (abs s P) | normal_form_ty_abs {P} : normal_form P -> normal_form (ty_abs P).
Scheme normal_form_ind' := Induction for normal_form Sort Prop with head_form_ind' := Induction for head_form Sort Prop.
Fact normal_form_ren_term {ζ ξ P} : normal_form P -> normal_form (ren_term ζ ξ P).
Proof.
move=> H.
move: P H ζ ξ.
apply: (normal_form_ind' (fun P _ => forall ζ ξ, normal_form (ren_term ζ ξ P)) (fun P _ => forall ζ ξ, head_form (ren_term ζ ξ P))); by eauto using normal_form, head_form.
Fact head_form_ren_term {ζ ξ P} : head_form P -> head_form (ren_term ζ ξ P).
Proof.
move=> H.
move: P H ζ ξ.
apply: (head_form_ind' (fun P _ => forall ζ ξ, normal_form (ren_term ζ ξ P)) (fun P _ => forall ζ ξ, head_form (ren_term ζ ξ P))); by eauto using normal_form, head_form.
Fixpoint erase (P: term) : pure_term := match P with | var x => pure_var x | app P Q => pure_app (erase P) (erase Q) | abs _ P => pure_abs (erase P) | ty_app P _ => erase P | ty_abs P => erase P end.
Fact erase_subst_term_var {P σ} : erase (subst_term σ var P) = erase P.
Proof.
elim: P σ; move=> /= *; rewrite ?subst_term_up_term_term_var ?subst_term_up_poly_type_term_var; by congruence.
Definition many_app (P: term) (Qs: list term) := fold_left app Qs P.
Definition many_ty_app (P: term) (ts: list poly_type) := fold_left ty_app ts P.
Definition many_ty_abs (n: nat) (P: term) := Nat.iter n ty_abs P.
Fact many_app_app {P Qs Qs'} : many_app P (Qs ++ Qs') = many_app (many_app P Qs) Qs'.
Proof.
by rewrite /many_app fold_left_app.
Fact many_ty_app_app {P ts ts'} : many_ty_app P (ts ++ ts') = many_ty_app (many_ty_app P ts) ts'.
Proof.
by rewrite /many_ty_app fold_left_app.
Definition many_pure_app (M: pure_term) (Ns: list pure_term) := fold_left pure_app Ns M.
Fact many_pure_app_app {M Ns Ns'} : many_pure_app M (Ns ++ Ns') = many_pure_app (many_pure_app M Ns) Ns'.
Proof.
by rewrite /many_pure_app fold_left_app.
Definition many_pure_term_abs (n: nat) (M: pure_term) := Nat.iter n pure_abs M.
Inductive argument : Type := | argument_term : term -> argument | argument_poly_type : poly_type -> argument.
Definition many_argument_app (P: term) (As: list argument) := fold_left (fun P A => match A with | argument_term Q => app P Q | argument_poly_type t => ty_app P t end) As P.
Fact many_argument_app_app {P As As'} : many_argument_app P (As ++ As') = many_argument_app (many_argument_app P As) As'.
Proof.
by rewrite /many_argument_app fold_left_app.
Fact erase_many_ty_abs {n P} : erase (many_ty_abs n P) = erase P.
Proof.
elim: n => /= *; by congruence.
Fact erase_many_ty_app {ts P} : erase (many_ty_app P ts) = erase P.
Proof.
elim: ts P; [done | by move=> > + ? /= => ->].
Fixpoint term_size (P: term) := match P with | var _ => 1 | app P Q => 1 + term_size P + term_size Q | abs _ P => 1 + term_size P | ty_app P _ => 1 + term_size P | ty_abs P => 1 + term_size P end.
Fact term_size_ren_term {ζ ξ P} : term_size (ren_term ζ ξ P) = term_size P.
Proof.
elim: P ζ ξ => /=; by congruence.
Fixpoint allfv_term (p: nat -> Prop) (P: term) := match P with | var x => p x | app P Q => allfv_term p P /\ allfv_term p Q | abs _ P => allfv_term (scons True p) P | ty_app P _ => allfv_term p P | ty_abs P => allfv_term p P end.

Fact head_form_ren_term {ζ ξ P} : head_form P -> head_form (ren_term ζ ξ P).
Proof.
move=> H.
move: P H ζ ξ.
apply: (head_form_ind' (fun P _ => forall ζ ξ, normal_form (ren_term ζ ξ P)) (fun P _ => forall ζ ξ, head_form (ren_term ζ ξ P))); by eauto using normal_form, head_form.
