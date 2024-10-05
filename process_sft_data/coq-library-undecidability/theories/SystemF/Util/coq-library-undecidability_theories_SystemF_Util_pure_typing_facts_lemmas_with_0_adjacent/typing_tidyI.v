Require Import List Lia Relation_Definitions Relation_Operators Operators_Properties.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts iipc2_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments funcomp {X Y Z} _ _ / _.
Arguments fresh_in _ _ /.
Inductive contains_step : poly_type -> poly_type -> Prop := | contains_step_subst {s t} : contains_step (poly_abs t) (subst_poly_type (scons s poly_var) t).
Definition contains := clos_refl_trans poly_type contains_step.
Inductive pure_typing : environment -> pure_term -> poly_type -> Prop := | pure_typing_pure_var n {Gamma x t t'} : nth_error (map (ren_poly_type (Nat.add n)) Gamma) x = Some t -> contains t t' -> pure_typing Gamma (pure_var x) (many_poly_abs n t') | pure_typing_pure_app n {Gamma M N s t t'} : pure_typing (map (ren_poly_type (Nat.add n)) Gamma) M (poly_arr s t) -> pure_typing (map (ren_poly_type (Nat.add n)) Gamma) N s -> contains t t' -> pure_typing Gamma (pure_app M N) (many_poly_abs n t') | pure_typing_pure_abs n {Gamma M s t} : pure_typing (s :: map (ren_poly_type (Nat.add n)) (Gamma)) M t -> pure_typing Gamma (pure_abs M) (many_poly_abs n (poly_arr s t)).
Definition pure_typable Gamma M := exists t, pure_typing Gamma M t.
Arguments pure_typable : simpl never.
Fixpoint tidy (t: poly_type) := match t with | poly_var _ => t | poly_arr s t => poly_arr (tidy s) (tidy t) | poly_abs t => if fresh_inb 0 t then ren_poly_type (scons 0 id) (tidy t) else (poly_abs (tidy t)) end.

Lemma typing_tidyI {Gamma P t} : typing Gamma P t -> exists Q, erase P = erase Q /\ typing (map tidy Gamma) Q (tidy t).
Proof.
elim: P Gamma t.
-
move=> x Gamma t /typingE Hx.
exists (var x).
constructor; first done.
apply: typing_var.
by rewrite nth_error_map Hx.
-
move=> P IHP Q IHQ Gamma t /typingE [?] /= [/IHP [P'] [->] {}IHP /IHQ [Q'] [->] {}IHQ].
exists (app P' Q').
constructor; first done.
apply: typing_app; by eassumption.
-
move=> s P IH Gamma t /typingE [?] /= [->] /IH [P'] [->] HP'.
exists (abs (tidy s) P').
constructor; first done.
by apply: typing_abs.
-
move=> P IH s Gamma t /typingE [t'] /= [->] /IH [P'] [->].
move=> /typing_contains.
apply.
by apply /contains_tidyI /rt_step /contains_step_subst.
-
move=> P IH Gamma t /typingE [t'] /= [->] /IH [P'] [->] /=.
case Hb: (fresh_inb _ _).
+
move=> /(typing_ren_poly_type (0 .: id)) => H.
exists (ren_term (0 .: id) id P').
constructor; first by rewrite erase_ren_term_id.
congr typing: H.
rewrite ?map_map.
apply: map_ext => ?.
by rewrite tidy_ren_poly_type ?poly_type_norm /= ren_poly_type_id.
+
move=> H.
exists (ty_abs P').
constructor; first done.
apply: typing_ty_abs.
congr typing: H.
rewrite ?map_map.
apply: map_ext => ?.
by apply: tidy_ren_poly_type.
