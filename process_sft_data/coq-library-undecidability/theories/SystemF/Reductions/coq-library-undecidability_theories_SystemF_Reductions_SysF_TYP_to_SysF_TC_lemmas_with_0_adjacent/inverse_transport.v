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

Lemma inverse_transport : SysF_TC (Gamma_M0, M_M0, t_M0) -> SysF_TYP M0.
Proof.
move=> /pure_typing_iff_type_assignment.
rewrite /Gamma_M0 /M_M0 /t_M0.
move=> /pure_typingE' [?] [?] [_] [/pure_typableI HM0 _].
have : exists Gamma, pure_typable Gamma M0.
{
elim: (pure_var_bound M0) ([poly_abs (poly_var 0)]) HM0.
-
move=> /= ? ?.
eexists.
by eassumption.
-
by move=> {}n IH Gamma /= /pure_typableE [?] /IH.
}
move=> [Gamma] [t] /pure_typing_to_typing [P] [->].
move=> /typing_to_type_assignment ?.
by exists Gamma, t.
