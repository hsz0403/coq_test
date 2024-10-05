Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts pure_typing_facts pure_typable_prenex.
Require Undecidability.SemiUnification.SemiU.
Module SU := SemiU.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Section LU2SemiU_to_SysF_TYP.
Variables SUs SUt0 SUt1 : SU.term.
Fixpoint SU_term_to_poly_type (s: SU.term) := match s with | SU.atom n => poly_var n | SU.arr s t => poly_arr (SU_term_to_poly_type s) (SU_term_to_poly_type t) end.
Definition SUs' := SU_term_to_poly_type SUs.
Definition SUt0' := SU_term_to_poly_type SUt0.
Definition SUt1' := SU_term_to_poly_type SUt1.
Definition N_W := pure_abs (many_pure_app (pure_var 2) [pure_var 0; pure_var 0]).
Definition M_W : pure_term := many_pure_app (pure_var 0) [N_W].
Definition t_0_W := (poly_arr (poly_arr (poly_var 0) (poly_var 0)) (poly_var 1)).
Definition t_1_W := poly_arr (poly_arr SUt0' SUt0') (poly_arr (poly_arr SUt1' SUt1') (poly_arr SUs' SUs')).
Definition n_W : nat := locked (poly_var_bound t_1_W).
Definition Gamma_W : list poly_type := [poly_abs (poly_abs t_0_W); many_poly_abs n_W t_1_W].
Definition HM_W1 := pure_typable_intro_prenex M_W t_0_W 2 is_simple_t_0_W closed_t_0_W.
Definition HM_W2 := pure_typable_intro_prenex (sval HM_W1) t_1_W n_W is_simple_t_1_W closed_t_1_W.
Section InverseTransport.
Local Arguments many_pure_app : simpl never.
Local Arguments map : simpl never.
Fixpoint prune (s: poly_type) : SU.term := match s with | poly_var x => SU.atom (1 + x) | poly_arr s t => SU.arr (prune s) (prune t) | poly_abs _ => SU.atom 0 end.
Fact substitute_prune_ex τ t : exists ψ, SU.substitute ψ (prune t) = prune (subst_poly_type τ t).
Proof.
exists (fun n=> if n is S n then prune (τ n) else SU.atom 0).
elim: t; [done | by move=> ? + ? /= => -> -> | done ].
Fact substitute_prune {σ t} : SU.substitute (funcomp prune σ) t = prune (subst_poly_type σ (SU_term_to_poly_type t)).
Proof.
elim: t; [done | by move=> ? + ? => /= -> -> ].
End InverseTransport.
Section Transport.
Variables φ ψ0 ψ1 : nat -> SU.term.
Variable Hφψ0 : SU.substitute ψ0 (SU.substitute φ SUs) = SU.substitute φ SUt0.
Variable Hφψ1 : SU.substitute ψ1 (SU.substitute φ SUs) = SU.substitute φ SUt1.
Definition t_x_W' := SU_term_to_poly_type (SU.substitute φ SUs).
Definition n_W' := locked (poly_var_bound (poly_arr t_x_W' t_x_W')).
Definition t_x_W : poly_type := many_poly_abs n_W' (poly_arr t_x_W' t_x_W').
Definition t_x_0_W : poly_type := SU_term_to_poly_type (SU.substitute φ SUt0).
Definition t_x_1_W : poly_type := SU_term_to_poly_type (SU.substitute φ SUt1).
Definition ts_0_W : list poly_type := map (fun n => SU_term_to_poly_type (φ n)) (rev (seq 0 n_W)).
Definition ts_1_W : list poly_type := map (fun n => SU_term_to_poly_type (ψ0 n)) (rev (seq 0 n_W')).
Definition ts_2_W : list poly_type := map (fun n => SU_term_to_poly_type (ψ1 n)) (rev (seq 0 n_W')).
Definition x_1_W : term := many_ty_app (var 0) ts_1_W.
Definition x_2_W : term := many_ty_app (var 0) ts_2_W.
Definition Q_W : term := abs t_x_W (many_ty_abs n_W' (app (app (many_ty_app (var 2) ts_0_W) x_1_W) x_2_W)).
Definition P_W : term := app (ty_app (ty_app (var 0) (poly_var 0)) t_x_W) Q_W.
Fact poly_var_bound_SUt0'_n_W : poly_var_bound SUt0' < n_W.
Proof.
rewrite /n_W /t_1_W /= -lock.
by lia.
Fact poly_var_bound_SUt1'_n_W : poly_var_bound SUt1' < n_W.
Proof.
rewrite /n_W /t_1_W /= -lock.
by lia.
Fact poly_var_bound_SUs'_n_W : poly_var_bound SUs' < n_W.
Proof.
rewrite /n_W /t_1_W /= -lock.
by lia.
Fact poly_arr_eq_eq {s t} : s = t -> poly_arr s s = poly_arr t t.
Proof.
by move=> ->.
End Transport.
End LU2SemiU_to_SysF_TYP.
End Argument.
Require Import Undecidability.Synthetic.Definitions.
Import SemiU.

Lemma is_simple_SU_term_to_poly_type {s} : is_simple (SU_term_to_poly_type s) <-> True.
Proof.
elim: s; [done | by move=> /= ? + ? + => -> ->].
