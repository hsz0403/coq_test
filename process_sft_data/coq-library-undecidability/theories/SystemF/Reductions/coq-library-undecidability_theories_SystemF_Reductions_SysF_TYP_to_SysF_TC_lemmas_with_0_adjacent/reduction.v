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

Theorem reduction : SysF_TYP ⪯ SysF_TC.
Proof.
exists (fun 'M0 => (Argument.Gamma_M0, Argument.M_M0 M0, Argument.t_M0)).
move=> M0.
constructor.
-
exact: Argument.transport.
-
exact: Argument.inverse_transport.
