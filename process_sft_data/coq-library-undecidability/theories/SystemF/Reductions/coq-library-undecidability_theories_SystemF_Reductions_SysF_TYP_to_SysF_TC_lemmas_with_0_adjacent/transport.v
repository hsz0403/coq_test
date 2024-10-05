Require Import List Lia Relation_Operators.
Import ListNotations.
Require Import Undecidability.SystemF.SysF.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts pure_typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Section SysF_TYP_to_SysF_TC.
Variables M0 : pure_term.
Definition Gamma_M0 := [poly_abs (poly_var 0)].
Definition M_M0 := pure_app (pure_var 0) (many_pure_term_abs (pure_var_bound M0) M0).
Definition t_M0 := poly_var 0.
End SysF_TYP_to_SysF_TC.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma transport : SysF_TYP M0 -> SysF_TC (Gamma_M0, M_M0, t_M0).
Proof.
move=> [Gamma] [t] /pure_typing_iff_type_assignment.
move=> /pure_typableI /pure_typable_many_pure_term_abs_allI [{}t].
move=> /(pure_typing_ren_pure_term id (Delta := Gamma_M0)).
rewrite ren_pure_term_id.
apply: unnest; first by case.
move=> /(pure_typing_pure_app_simpleI (M := pure_var 0) (t := t_M0)).
apply: unnest.
{
apply: (pure_typing_pure_var 0); first by reflexivity.
apply: rt_step.
by apply: contains_step_subst.
}
move=> /pure_typing_to_typing /= [P] [HP] /typing_to_type_assignment.
by rewrite -HP.
