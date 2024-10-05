Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts term_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments funcomp {X Y Z} _ _ / _.
Inductive typing : environment -> term -> poly_type -> Prop := | typing_var {Gamma x t} : nth_error Gamma x = Some t -> typing Gamma (var x) t | typing_app {Gamma P Q s t} : typing Gamma P (poly_arr s t) -> typing Gamma Q s -> typing Gamma (app P Q) t | typing_abs {Gamma P s t} : typing (s :: Gamma) P t -> typing Gamma (abs s P) (poly_arr s t) | typing_ty_app {Gamma P s t} : typing Gamma P (poly_abs s) -> typing Gamma (ty_app P t) (subst_poly_type (scons t poly_var) s) | typing_ty_abs {Gamma P s} : typing (map (ren_poly_type S) Gamma) P s -> typing Gamma (ty_abs P) (poly_abs s).
Fact typing_many_argument_subterm {Gamma P As t} : typing Gamma (many_argument_app P As) t -> exists t', typing Gamma P t'.
Proof.
elim: As P t; first by (move=> *; eexists; eassumption).
move=> [|] P As IH > /= /IH [?] /typingE; clear; by firstorder done.

Lemma typing_many_ty_appI {Gamma P n t ts} : length ts = n -> typing Gamma P (many_poly_abs n t) -> typing Gamma (many_ty_app P ts) (subst_poly_type (fold_right scons poly_var (rev ts)) t).
Proof.
elim: n Gamma P t ts.
-
move=> ? ? ? [|]; last done.
move=> _ /=.
congr typing.
by rewrite subst_poly_type_poly_var.
-
move=> n IH Gamma P t.
elim /rev_ind; first done.
move=> s ts'.
rewrite app_length /many_poly_abs -iter_last -/(many_poly_abs _ _) /=.
move=> ? ?.
have /IH {}IH : length ts' = n by lia.
move=> /IH {}IH.
rewrite rev_unit many_ty_app_app /=.
move: IH => /= => /typing_ty_app => /(_ s).
congr typing.
rewrite ?poly_type_norm.
apply: ext_poly_type => [[|x]]; first done.
by rewrite /= ?poly_type_norm /= subst_poly_type_poly_var.
