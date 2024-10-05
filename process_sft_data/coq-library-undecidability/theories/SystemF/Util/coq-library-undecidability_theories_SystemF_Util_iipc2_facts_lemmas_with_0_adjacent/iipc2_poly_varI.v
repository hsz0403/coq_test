Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Lemma iipc2_poly_varI x {Gamma ts ss y} : nth_error Gamma x = Some (many_poly_abs (length ts) (many_poly_arr ss (poly_var (length ts + y)))) -> Forall (iipc2 Gamma) (map (subst_poly_type (fold_right scons poly_var (rev ts))) ss) -> iipc2 Gamma (poly_var y).
Proof.
move=> /typing_var /typing_many_ty_appI => /(_ ts ltac:(done)).
rewrite subst_poly_type_many_poly_arr /subst_poly_type -rev_length fold_right_length_ts -/subst_poly_type.
move=> /iipc2I.
move: (map _ ss) => {}ss.
move: (poly_var y) => t.
elim: ss t; first done.
by move=> s ss IH t /= [?] /typing_app H /Forall_consP [[?] /H{H} /iipc2I /IH].
