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

Lemma SU_term_to_poly_type_SU_substitute {ζ t} : subst_poly_type (fun x : nat => SU_term_to_poly_type (ζ x)) (SU_term_to_poly_type t) = SU_term_to_poly_type (SU.substitute ζ t).
Proof.
Admitted.

Lemma subst_poly_type_SU_term_to_poly_type {ζ n t} : poly_var_bound (SU_term_to_poly_type t) < n -> subst_poly_type (fold_right scons poly_var (map (fun x => SU_term_to_poly_type (ζ x)) (seq 0 n))) (SU_term_to_poly_type t) = SU_term_to_poly_type (SU.substitute ζ t).
Proof.
move=> ?.
rewrite subst_poly_type_map_seq; first by lia.
Admitted.

Fact poly_arr_eq_eq {s t} : s = t -> poly_arr s s = poly_arr t t.
Proof.
Admitted.

Lemma typing_x_1_W : (forall Gamma, typing (many_poly_abs n_W' (poly_arr t_x_W' t_x_W') :: Gamma) x_1_W (poly_arr t_x_0_W t_x_0_W)).
Proof using Hφψ0.
move=> Gamma.
rewrite /x_1_W.
evar (t: poly_type).
have := @typing_var (many_poly_abs n_W' (poly_arr t_x_W' t_x_W') :: Gamma) 0 t.
subst t.
move=> /(_ ltac:(reflexivity)) /typing_many_ty_appI => /(_ ts_1_W).
apply: unnest.
{
by rewrite /ts_1_W map_length rev_length seq_length.
}
congr typing => /=.
apply: poly_arr_eq_eq.
rewrite /ts_1_W /t_x_W' /t_x_0_W -Hφψ0.
rewrite -map_rev rev_involutive.
apply: subst_poly_type_SU_term_to_poly_type.
rewrite /n_W' /t_x_W' -lock /=.
Admitted.

Lemma typing_x_2_W : (forall Gamma, typing (many_poly_abs n_W' (poly_arr t_x_W' t_x_W') :: Gamma) x_2_W (poly_arr t_x_1_W t_x_1_W)).
Proof using Hφψ1.
move=> Gamma.
rewrite /x_2_W.
evar (t: poly_type).
have := @typing_var (many_poly_abs n_W' (poly_arr t_x_W' t_x_W') :: Gamma) 0 t.
subst t.
move=> /(_ ltac:(reflexivity)) => /typing_many_ty_appI => /(_ ts_2_W).
apply: unnest.
{
by rewrite /ts_2_W map_length rev_length seq_length.
}
congr typing => /=.
apply: poly_arr_eq_eq.
rewrite /ts_2_W /t_x_W' /t_x_1_W -Hφψ1.
rewrite -map_rev rev_involutive.
apply: subst_poly_type_SU_term_to_poly_type.
rewrite /n_W' /t_x_W' -lock /=.
Admitted.

Lemma typing_Q_W : (forall Gamma, typing (many_poly_abs n_W' (poly_arr t_x_W' t_x_W') :: Gamma) x_1_W (poly_arr t_x_0_W t_x_0_W)) -> (forall Gamma, typing (many_poly_abs n_W' (poly_arr t_x_W' t_x_W') :: Gamma) x_2_W (poly_arr t_x_1_W t_x_1_W)) -> typing Gamma_W Q_W (poly_arr t_x_W t_x_W).
Proof.
move=> H1 H2.
apply /typing_abs /typing_many_ty_absI.
apply: (typing_app (s := (poly_arr t_x_1_W t_x_1_W))); [apply: (typing_app (s := (poly_arr t_x_0_W t_x_0_W))) |].
-
evar (t : poly_type).
have := @typing_var (map (ren_poly_type (Nat.add n_W')) (t_x_W :: Gamma_W)) 2 t.
subst t.
move=> /(_ ltac:(reflexivity)).
rewrite ren_poly_type_many_poly_abs.
move /typing_many_ty_appI => /(_ ts_0_W).
apply: unnest.
{
by rewrite /ts_0_W map_length rev_length seq_length.
}
congr typing.
rewrite /t_1_W /= -map_rev rev_involutive.
congr poly_arr; [| congr poly_arr]; apply: poly_arr_eq_eq.
+
have := poly_var_bound_SUt0'_n_W.
rewrite /t_x_0_W /SUt0' /ts_0_W.
move=> ?.
rewrite ren_poly_type_poly_var_bound; first by lia.
by apply: subst_poly_type_SU_term_to_poly_type.
+
have := poly_var_bound_SUt1'_n_W.
rewrite /t_x_1_W /SUt1' /ts_0_W.
move=> ?.
rewrite ren_poly_type_poly_var_bound; first by lia.
by apply: subst_poly_type_SU_term_to_poly_type.
+
have := poly_var_bound_SUs'_n_W.
rewrite /t_x_W' /SUs' /ts_0_W.
move=> ?.
rewrite ren_poly_type_poly_var_bound; first by lia.
by apply: subst_poly_type_SU_term_to_poly_type.
-
rewrite /(map _ (_ :: _)) -/(map _ _).
move: (map _ Gamma_W) => Gamma.
rewrite /t_x_W ren_poly_type_many_poly_abs ren_poly_type_poly_var_bound; first by (rewrite /n_W' -lock /=; lia).
by apply: H1.
-
rewrite /(map _ (_ :: _)) -/(map _ _).
move: (map _ Gamma_W) => Gamma.
rewrite /t_x_W ren_poly_type_many_poly_abs ren_poly_type_poly_var_bound; first by (rewrite /n_W' -lock /=; lia).
Admitted.

Lemma erase_P_W : erase P_W = M_W.
Proof.
Admitted.

Lemma typing_P_W : typing Gamma_W Q_W (poly_arr t_x_W t_x_W) -> typing Gamma_W P_W (poly_var 0).
Proof.
rewrite /P_W.
apply: typing_app.
Admitted.

Lemma pure_typable_M_W : typing Gamma_W P_W (poly_var 0) -> pure_typable Gamma_W M_W.
Proof.
move=> /typing_to_pure_typing /pure_typableI.
Admitted.

Lemma transport : SU.LU2SemiU (SUs, SUt0, SUt1) -> SysF_TYP (sval HM_W2).
Proof.
move=> [φ] [ψ0] [ψ1] [Hφψ0 HHφψ1].
apply: (SysF_TYPI (map tidy [])).
apply /(svalP HM_W2) /(svalP HM_W1).
have := iffRL (pure_typable_tidy_iff _ (Gamma1 := [])).
move=> /(_ [many_poly_abs 2 t_0_W; many_poly_abs n_W t_1_W]).
apply; first by apply: prenex_Gamma_W.
apply: (pure_typable_M_W φ ψ0 ψ1).
apply: typing_P_W.
Admitted.

Theorem reduction : LU2SemiU ⪯ SysF_TYP.
Proof.
exists (fun '(s, t0, t1) => (sval (Argument.HM_W2 s t0 t1))).
move=> [[s t0] t1].
constructor.
-
exact: Argument.transport.
-
exact: Argument.inverse_transport.
