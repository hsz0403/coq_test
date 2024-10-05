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
Admitted.

Lemma typing_weakening {Gamma Gamma' P t} : incl Gamma Gamma' -> typing Gamma P t -> exists ξ, typing Gamma' (ren_term id ξ P) t.
Proof.
move=> /incl_nth_error [ξ] + /typing_ren_term' H => /H ?.
eexists.
Admitted.

Lemma typing_normal_form_poly_arrE {Gamma P s t}: normal_form P -> typing Gamma P (poly_arr s t) -> exists Q, normal_form Q /\ term_size Q <= term_size P + 2 /\ typing (s :: Gamma) Q t.
Proof.
case.
-
move=> {}P HP.
move=> /(@typing_ren_term' S) => /(_ (s :: Gamma) ltac:(done)) H.
exists (app (ren_term id S P) (var 0)).
constructor; last constructor.
+
apply: normal_form_head_form.
apply: head_form_app; [by apply: head_form_ren_term | by eauto using normal_form, head_form ].
+
rewrite /= term_size_ren_term.
by lia.
+
apply: typing_app; [by eassumption | by apply: typing_var].
-
move=> > ? /typingE [?] [[-> ->]] ?.
eexists.
constructor; first by eassumption.
move=> /=.
constructor; [by lia | done].
-
Admitted.

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
Admitted.

Lemma typing_many_app_arguments {Gamma P Qs t ss t'} : length Qs = length ss -> typing Gamma (many_app P Qs) t -> typing Gamma P (many_poly_arr ss t') -> Forall2 (typing Gamma) Qs ss.
Proof.
elim: Qs P t ss t'.
-
move=> ? ? [|] *; [by constructor | done].
-
move=> Q Qs IH P ? [|? ?] ?; first done.
move=> [/IH {}IH] /= /copy [/IH {}IH].
rewrite -many_argument_app_map_argument_term.
move=> /typing_many_argument_subterm [?].
move=> /copy [/typingE [?] [+ ?]].
move=> /typing_functional H + /H{H} [? ?].
subst.
move=> /IH ?.
Admitted.

Theorem typing_to_type_assignment {Gamma P t} : typing Gamma P t -> type_assignment Gamma (erase P) t.
Proof.
elim.
-
move=> *.
by apply: type_assignment_var.
-
move=> * /=.
apply: type_assignment_app; by eassumption.
-
move=> * /=.
by apply: type_assignment_abs.
-
move=> * /=.
by apply: type_assignment_inst.
-
move=> * /=.
Admitted.

Theorem typing_of_type_assignment {Gamma M t} : type_assignment Gamma M t -> exists P, M = erase P /\ typing Gamma P t.
Proof.
elim.
-
move=> ? x ? ?.
exists (var x).
constructor; [done | by apply: typing_var].
-
move=> > ? [P [? ?]] ? [Q [? ?]].
exists (app P Q).
subst.
constructor; [done | by apply: typing_app; eassumption].
-
move=> ? ? s ? ? [P [? ?]].
exists (abs s P).
subst.
constructor; [done | by apply: typing_abs].
-
move=> ? ? ? {}t ? [P [? ?]].
exists (ty_app P t).
subst.
constructor; [done | by apply: typing_ty_app].
-
move=> > ? [P [? ?]].
exists (ty_abs P).
subst.
constructor; [done | by apply: typing_ty_abs].
