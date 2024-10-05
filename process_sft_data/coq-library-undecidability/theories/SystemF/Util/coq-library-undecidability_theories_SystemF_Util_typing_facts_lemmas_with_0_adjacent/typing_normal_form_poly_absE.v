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

Lemma typing_normal_form_poly_absE {Gamma P t}: normal_form P -> typing Gamma P (poly_abs t) -> forall x, exists Q, normal_form Q /\ term_size Q <= term_size P + 2 /\ typing Gamma Q (ren_poly_type (x .: id) t).
Proof.
case.
-
move=> {}P ? HP x.
exists (ty_app P (poly_var x)).
constructor; first by eauto using normal_form, head_form.
constructor; first by move=> /=; lia.
move: HP => /typing_ty_app => /(_ (poly_var x)).
congr typing.
rewrite -[RHS]subst_poly_type_poly_var ?poly_type_norm.
apply: ext_poly_type.
by case.
-
by move=> > ? /typingE [?] [].
-
move=> {}P ? /typingE [?] [[<-]] + x.
move=> /(typing_ren_poly_type (x .: id)) HP.
exists (ren_term (x .: id) id P).
constructor; first by apply: normal_form_ren_term.
rewrite term_size_ren_term /=.
constructor; first by lia.
move: HP.
congr typing.
rewrite map_map -[RHS]map_id.
apply: map_ext.
move=> ?.
by rewrite ?poly_type_norm ren_poly_type_id'.
