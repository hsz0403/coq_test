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

Lemma typing_subst_term {Gamma Delta P t} σ : typing Gamma P t -> (forall n s, nth_error Gamma n = Some s -> typing Delta (σ n) s) -> typing Delta (subst_term poly_var σ P) t.
Proof.
move=> H.
elim: H σ Delta.
-
by move=> > + > H => /H.
-
move=> > ? IH1 ? IH2 > H /=.
apply: typing_app; [by apply: IH1 | by apply: IH2].
-
move=> > ? IH > H /=.
rewrite subst_poly_type_poly_var ?term_norm.
apply: typing_abs.
apply: IH => [[|n]] ?.
+
move=> /= [<-].
by apply: typing_var.
+
move=> /H /typing_ren_term.
apply.
by case.
-
move=> > _ IH > ? /=.
rewrite subst_poly_type_poly_var.
by apply /typing_ty_app /IH.
-
move=> {}Gamma > _ IH > H /=.
under ext_term => [? | ?] do [rewrite up_poly_type_poly_type_poly_var |].
apply /typing_ty_abs /IH => n' s'.
rewrite nth_error_map.
case Hn': (nth_error Gamma n'); last done.
move: Hn' => /H {}H [<-].
by apply: typing_ren_poly_type.
