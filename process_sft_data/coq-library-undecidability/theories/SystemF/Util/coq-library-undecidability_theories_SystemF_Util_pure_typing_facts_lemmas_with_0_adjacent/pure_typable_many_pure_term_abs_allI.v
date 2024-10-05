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

Lemma pure_typable_many_pure_term_abs_allI M {Gamma} : pure_typable Gamma M -> pure_typable [] (many_pure_term_abs (pure_var_bound M) M).
Proof.
have := pure_var_boundP M.
move: (pure_var_bound M) => n.
elim: Gamma n M.
-
elim; first done.
move=> n IH M HnM [tM].
move=> /(pure_typing_ren_pure_term id (Delta := [poly_var 0])).
apply: unnest; first by case.
rewrite ren_pure_term_id.
move=> /(pure_typing_pure_abs 0 (Gamma := [])) /pure_typableI /IH.
rewrite /many_pure_term_abs (ltac:(lia) : S n = n + 1) -iter_plus.
apply.
move=> /=.
apply: allfv_pure_term_impl HnM.
case; first done.
move=> /=.
by lia.
-
move=> s Gamma IH [|n] M.
+
move=> HM [tM].
move=> /(pure_typing_ren_pure_term_allfv_pure_term id (Delta := [])).
rewrite ren_pure_term_id.
apply: unnest; first by apply: allfv_pure_term_impl HM; lia.
by move=> /pure_typableI.
+
move=> HnM [tM].
rewrite -[Gamma]map_ren_poly_type_id.
move=> /(pure_typing_pure_abs 0) /pure_typableI /IH.
rewrite /many_pure_term_abs (ltac:(lia) : S n = n + 1) -iter_plus.
apply.
move=> /=.
apply: allfv_pure_term_impl HnM.
case; first done.
move=> /=.
by lia.
