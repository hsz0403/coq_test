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

Lemma typingE {Gamma P t} : typing Gamma P t -> match P with | var x => nth_error Gamma x = Some t | app P Q => exists s, typing Gamma P (poly_arr s t) /\ typing Gamma Q s | abs s P => exists t', t = poly_arr s t' /\ typing (s :: Gamma) P t' | ty_app P t' => exists s, t = (subst_poly_type (t' .: poly_var) s) /\ typing Gamma P (poly_abs s) | ty_abs P => exists s, t = (poly_abs s) /\ typing (map (ren_poly_type S) Gamma) P s end.
Proof.
Admitted.

Lemma typing_ren_poly_type {Gamma P t} ξ : typing Gamma P t -> typing (map (ren_poly_type ξ) Gamma) (ren_term ξ id P) (ren_poly_type ξ t).
Proof.
move=> /(typing_subst_poly_type (ξ >> poly_var)).
congr typing.
-
apply: map_ext => ?.
by rewrite -[RHS]subst_poly_type_poly_var ?poly_type_norm.
-
by rewrite -[RHS]subst_term_poly_var_var ?term_norm.
-
Admitted.

Lemma typing_functional {Gamma P t t'} : typing Gamma P t -> typing Gamma P t' -> t = t'.
Proof.
elim: P Gamma t t'.
-
move=> > /typingE + /typingE.
by congruence.
-
move=> P IHP Q IHQ > /typingE [?] [/IHP {}IHP /IHQ {}IHQ].
move=> /typingE [?] [/IHP {}IHP /IHQ {}IHQ].
by congruence.
-
move=> > IH > /typingE [?] [-> /IH {}IH].
move=> /typingE [?] [-> /IH].
by congruence.
-
move=> > IH > /typingE [?] [-> /IH {}IH].
move=> /typingE [?] [-> /IH].
by congruence.
-
move=> > IH > /typingE [?] [-> /IH {}IH].
move=> /typingE [?] [-> /IH].
Admitted.

Fact typing_many_argument_subterm {Gamma P As t} : typing Gamma (many_argument_app P As) t -> exists t', typing Gamma P t'.
Proof.
elim: As P t; first by (move=> *; eexists; eassumption).
Admitted.

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
Admitted.

Lemma typing_ty_appI {Gamma P t s s'}: typing Gamma P (poly_abs s) -> t = (subst_poly_type (s' .: poly_var) s) -> typing Gamma (ty_app P s') t.
Proof.
move=> + ->.
Admitted.

Lemma typing_many_ty_absI {n Gamma P t}: typing (map (ren_poly_type (Nat.add n)) Gamma) P t -> typing Gamma (many_ty_abs n P) (many_poly_abs n t).
Proof.
elim: n Gamma P t.
-
move=> >.
under map_ext => ? do rewrite /= ren_poly_type_id.
by rewrite map_id.
-
move=> n IH > H /=.
apply: typing_ty_abs.
apply: IH.
move: H.
congr typing.
rewrite map_map.
apply: map_ext.
move=> ?.
rewrite ?poly_type_norm.
apply: extRen_poly_type.
move=> ?.
rewrite /funcomp /=.
Admitted.

Lemma typing_allfv_term_in_environment {Gamma P t} : typing Gamma P t -> allfv_term (fun x => exists s, nth_error Gamma x = Some s) P.
Proof.
elim => /=.
-
move=> > ->.
by eexists.
-
done.
-
move=> > ?.
apply: allfv_term_impl.
by case.
-
done.
-
move=> > ?.
apply: allfv_term_impl => ?.
rewrite nth_error_map.
case: (nth_error _ _); last by case.
move=> *.
Admitted.

Lemma typing_ren_allfv_term {ξ Gamma Gamma' P t} : (allfv_term (fun x => nth_error Gamma x = nth_error Gamma' (ξ x)) P) -> typing Gamma P t -> typing Gamma' (ren_term id ξ P) t.
Proof.
elim: P ξ Gamma Gamma' t.
-
move=> > /= + /typingE => -> ?.
by apply: typing_var.
-
move=> ? IH1 ? IH2 > /= [/IH1 {}IH1 /IH2 {}IH2].
move=> /typingE [?] [/IH1 ? /IH2 ?] /=.
apply: typing_app; by eassumption.
-
move=> > IH > /= H /typingE [?] [->] /IH /= {}IH.
rewrite ren_poly_type_id.
apply: typing_abs.
apply: IH.
apply: allfv_term_impl H.
by case.
-
move=> > IH > /IH {}IH.
move=> /typingE [?] [->] /IH {}IH /=.
rewrite ren_poly_type_id.
by apply: typing_ty_app.
-
move=> > IH > /= H.
move=> /typingE [?] [->] /IH {}IH /=.
apply: typing_ty_abs.
under extRen_term.
+
move=> ?.
rewrite upRen_poly_type_poly_type_id.
over.
+
move=> ?.
rewrite /upRen_poly_type_term.
over.
+
apply: IH.
apply: allfv_term_impl H => ?.
rewrite ?nth_error_map.
Admitted.

Lemma typing_ren_term {ξ Gamma Delta P t} : (forall n s, nth_error Gamma n = Some s -> nth_error Delta (ξ n) = Some s) -> typing Gamma P t -> typing Delta (ren_term id ξ P) t.
Proof.
move=> H /copy [/typing_allfv_term_in_environment HP] /typing_ren_allfv_term.
apply.
Admitted.

Lemma typing_ren_term' {ξ Gamma Delta P t} : (forall n, nth_error Gamma n = nth_error Delta (ξ n)) -> typing Gamma P t -> typing Delta (ren_term id ξ P) t.
Proof.
move=> H /typing_ren_term.
apply => ? ?.
Admitted.

Lemma typing_subst_poly_type {Gamma P t} σ : typing Gamma P t -> typing (map (subst_poly_type σ) Gamma) (subst_term σ var P) (subst_poly_type σ t).
Proof.
elim: P Gamma t σ.
-
move=> > /typingE ? /=.
apply: typing_var.
by apply: map_nth_error.
-
move=> ? IH1 ? IH2 > /typingE [? [? ?]] /=.
apply: typing_app; last by apply: IH2; eassumption.
rewrite -/(subst_poly_type _ (poly_arr _ _)).
by apply: IH1.
-
move=> s P IH > /typingE [?] [-> ?] /=.
apply: typing_abs.
rewrite -/(map _ (_ :: _)).
rewrite ?term_norm.
by apply: IH.
-
move=> P IH s Gamma t σ /typingE [t'] [-> /IH] /=.
move=> /(_ σ) /typing_ty_app => /(_ (subst_poly_type σ s)).
congr typing.
rewrite ?poly_type_norm.
apply: ext_poly_type => [[|x]]; first done.
by rewrite /= ?poly_type_norm /= subst_poly_type_poly_var.
-
move=> P IH Gamma t σ /typingE [?] [-> /IH {}IH] /=.
apply: typing_ty_abs.
have := IH (poly_var 0 .: σ >> ren_poly_type S).
congr typing.
rewrite ?map_map.
apply: map_ext.
move=> ?.
by rewrite ?poly_type_norm.
