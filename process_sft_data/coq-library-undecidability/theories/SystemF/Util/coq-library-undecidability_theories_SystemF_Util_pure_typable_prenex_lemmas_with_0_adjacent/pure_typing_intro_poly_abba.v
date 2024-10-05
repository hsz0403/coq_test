Require Import List Lia Relation_Definitions Relation_Operators Operators_Properties.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts pure_term_facts term_facts typing_facts iipc2_facts pure_typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition K' M N := pure_app (pure_abs (ren_pure_term S M)) N.
Fixpoint leftmost_poly_var (t: poly_type) := match t with | poly_var x => Some x | poly_arr s t => leftmost_poly_var s | poly_abs t => if leftmost_poly_var t is Some (S x) then Some x else None end.
Fixpoint leftmost_path_length (t: poly_type) := match t with | poly_var x => 0 | poly_arr s t => 1 + leftmost_path_length s | poly_abs t => leftmost_path_length t end.
Definition Mω := pure_abs (pure_app (pure_var 0) (pure_var 0)).
Definition M_Wells N := pure_abs (K' (pure_var 0) (K' (pure_abs (pure_app (pure_var 1) (pure_app (pure_var 1) (pure_var 0)))) N)).
Definition M_Wells_J N := pure_app (pure_abs (K' (pure_app (pure_var 0) (pure_var 0)) (pure_app (pure_var 0) Mω))) (M_Wells N).
Ltac first_pure_typingE := match goal with | |- pure_typing _ (pure_app _ _) (poly_var _) -> _ => move=> /pure_typingE' [?] [?] [+] [+] ? | |- pure_typing _ (pure_app _ _) (poly_arr _ _) -> _ => move=> /pure_typingE' [?] [?] [+] [+] ? | |- pure_typing _ (pure_app _ _) _ -> _ => move=> /pure_typingE [?] [?] [?] [?] [+] [+] [? ?] | |- pure_typing _ (pure_abs _) (poly_arr _ _) -> _ => move=> /pure_typingE' | |- pure_typing _ (pure_abs _) _ -> _ => move=> /pure_typingE [?] [?] [?] [+ ?] | |- pure_typing _ (pure_var _) (poly_var _) -> _ => move=> /pure_typingE' [?] [[?]] ? | |- pure_typing _ (pure_var _) (poly_arr _ _) -> _ => move=> /pure_typingE' [?] [[?]] ? | |- pure_typing _ (pure_var _) _ -> _ => move=> /pure_typingE [?] [?] [?] [[?]] [? ?] | |- pure_typing _ (K' _ _) _ -> _ => move=> /pure_typing_K'E [] | |- pure_typable _ (K' _ _) -> _ => move=> /pure_typable_K'E [] | |- pure_typable _ (pure_var _) -> _ => move=> _ | |- pure_typable _ (pure_app _ _) -> _ => move=> /pure_typableE [?] [?] [] | |- pure_typable _ (pure_abs _) -> _ => move=> /pure_typableE [?] end.
Ltac simplify_poly_type_eqs := match goal with | H : contains (poly_var _) _ |- _ => move: H => /containsE ? | H : contains (poly_arr _ _) _ |- _ => move: H => /containsE ? | H : contains (many_poly_abs _ (poly_arr _ _)) (poly_arr _ _) |- _ => move: H => /contains_poly_arrE [?] [?] [? ?] | H : contains (subst_poly_type (fold_right scons poly_var _) _) _ |- _ => move /contains_subst_poly_type_fold_rightE in H; rewrite ?many_poly_abs_many_poly_abs in H | H : many_poly_abs _ (poly_var _) = subst_poly_type _ _ |- _ => move: H => /many_poly_abs_poly_var_eq_subst_poly_typeE => [[?]] [?] [?] [? ?] | H : contains (ren_poly_type _ (ren_poly_type _ _)) _ |- _ => rewrite ?renRen_poly_type /= in H | H : contains (ren_poly_type _ (many_poly_abs ?n (poly_var (?n + _)))) _ |- _ => rewrite ren_poly_type_many_poly_abs /= iter_up_ren in H | H : contains (ren_poly_type _ (many_poly_abs ?n (poly_arr (poly_var (?n + _)) (poly_var (?n + _))))) _ |- _ => rewrite ren_poly_type_many_poly_abs /= ?iter_up_ren in H | H : contains (many_poly_abs ?n (poly_var (?n + _))) _ |- _ => move: H => /contains_many_poly_abs_free [?] [?] [? ?] | H : poly_arr _ _ = many_poly_abs ?n _ |- _ => (have ? : n = 0 by move : (n) H; case); subst n; rewrite /= in H | H : many_poly_abs ?n _ = poly_var _ |- _ => (have ? : n = 0 by move : (n) H; case); subst n; rewrite /= in H | H : poly_var _ = poly_var _ |- _ => move: H => [?] end.
Arguments funcomp {X Y Z} _ _ / _.
Definition poly_abba := poly_abs (poly_abs (poly_arr (poly_var 1) (poly_arr (poly_var 0) (poly_arr (poly_var 0) (poly_var 1))))).
Fixpoint trace_poly_type (e: nat) (t: poly_type) : pure_term := match t with | poly_var x => pure_var x | poly_arr s t => pure_app (pure_app (pure_var e) (trace_poly_type e t)) (trace_poly_type e s) | poly_abs _ => pure_var 0 end.
Module pure_typable_intro_prenex_aux.
End pure_typable_intro_prenex_aux.
Import pure_typable_intro_prenex_aux.

Theorem pure_typing_intro_poly_abba M : { N | forall Gamma, pure_typable (map tidy (poly_abba :: Gamma)) M <-> pure_typable (map tidy Gamma) N }.
Proof.
pose N0 := (pure_abs (pure_abs (pure_abs (pure_abs ( K' (pure_var 2) (K' (pure_app (pure_var 3) (pure_var 0)) (pure_app (pure_var 3) (pure_var 1)))))))).
pose N1 := (pure_abs (K' (pure_app (pure_var 0) (pure_var 1)) (many_pure_app (pure_var 0) [pure_var 3; pure_var 2; pure_var 2; pure_var 2]))).
pose N2 := pure_app (ren_pure_term (Nat.add 3) (pure_abs M)) (pure_app N1 N0).
have [N2' HN2'] := pure_typable_intro_poly_bot N2.
have [N2'' HN2''] := pure_typable_intro_poly_var_0 N2'.
exists N2'' => Gamma.
constructor.
-
move=> [tM] HtM.
apply /HN2'' /HN2' => {HN2'' HN2'}.
eexists.
apply: (pure_typing_pure_app_simpleI (s := poly_abba)).
+
move=> /=.
apply: pure_typing_pure_abs_simpleI.
move: HtM => /(pure_typing_ren_poly_type S) HtM.
apply: pure_typing_ren_pure_term; first by eassumption.
move=> [|]; first done.
move=> ? ? /= <-.
congr nth_error.
rewrite ?map_map.
apply: map_ext => ?.
by rewrite tidy_ren_poly_type.
+
apply: (pure_typing_pure_app_simpleI (s := poly_abs (poly_abs (poly_arr (poly_arr (poly_var 0) (poly_var 0)) (poly_arr (poly_var 1) (poly_arr (poly_var 0) (poly_arr (poly_var 0) (poly_var 1)))))))).
*
apply: pure_typing_pure_abs_simpleI.
apply: pure_typing_K'I.
**
apply: (pure_typing_pure_app 2 (s := poly_arr (poly_var 0) (poly_var 0))).
***
apply: (pure_typing_pure_var 0); first by reflexivity.
apply: rt_trans; apply: rt_step; apply: contains_stepI; first done.
by rewrite /= ?poly_type_norm subst_poly_type_poly_var.
***
apply: (pure_typing_pure_var 0); first by reflexivity.
constructor.
by apply: contains_stepI.
***
by apply: rt_refl.
**
exists (poly_var 0).
do 4 (apply: pure_typing_pure_app_simpleI; last by apply: pure_typing_pure_var_simpleI).
move=> /=.
apply: (pure_typing_pure_var 0); first by reflexivity.
apply: rt_trans; apply: rt_step; apply: contains_stepI; first done.
by rewrite /= ?poly_type_norm subst_poly_type_poly_var.
*
apply: (pure_typing_pure_abs 2).
do 3 (apply: pure_typing_pure_abs_simpleI).
apply: pure_typing_K'I; first by apply: pure_typing_pure_var_simpleI.
exists (poly_var 0).
apply: pure_typing_K'I; first by apply: pure_typing_pure_app_simpleI; apply: pure_typing_pure_var_simpleI.
exists (poly_var 0).
by apply: pure_typing_pure_app_simpleI; apply: pure_typing_pure_var_simpleI.
-
move /HN2'' /HN2' => {HN2'' HN2'}.
rewrite /N2 /N1 /N0 /= => {N2 N1 N0}.
do ? first_pure_typingE.
move=> HM.
do ? first_pure_typingE.
subst.
do ? (simplify_poly_type_eqs; subst).
do ? (match goal with H : many_poly_abs _ (poly_arr _ _) = subst_poly_type _ _ |- _ => move: H end).
move=> /many_poly_abs_poly_arr_eq_subst_poly_typeE [].
{
move=> [?] [? ?].
subst.
do ? (simplify_poly_type_eqs; subst).
done.
}
move=> [?] [?] [? ?].
subst.
do ? (simplify_poly_type_eqs; subst).
do 2 (match goal with H : _ = fold_right scons poly_var _ (length _ + _) |- _ => move: H end).
do 2 (rewrite fold_right_length_ts_ge; first by lia).
move=> ? ?.
do ? (simplify_poly_type_eqs; subst).
match goal with H : contains _ (poly_arr _ _) |- _ => move: H end.
rewrite ren_poly_type_many_poly_abs /=.
move=> /contains_poly_arrE [?] [?] [? ?].
subst.
match goal with H : many_poly_abs _ _ = subst_poly_type _ _ |- _ => move: H end.
rewrite ?poly_type_norm ?subst_poly_type_many_poly_abs /= ?iter_up_poly_type_poly_type.
move=> /many_poly_abs_eqE'' /(_ ltac:(done)) [?] [? ?].
subst.
do ? (simplify_poly_type_eqs; subst).
move: HM => /=.
set s := (s in pure_typing (s :: _) _ _).
set Gamma' := (Gamma' in pure_typing (s :: _ :: _ :: _ :: Gamma') _ _).
move=> /(pure_typing_ren_pure_term_allfv_pure_term (scons 0 (scons 0 (scons 0 (scons 0 S)))) (Delta := s :: Gamma')).
apply: unnest.
{
rewrite allfv_pure_term_ren_pure_term /=.
apply: allfv_pure_term_TrueI.
by case.
}
rewrite renRen_pure_term /= ren_pure_term_id'; first by case.
subst Gamma'.
have : pure_typing [poly_abba] (pure_var 0) (tidy s).
{
have Habba : [poly_abba] = map tidy [poly_abba] by done.
rewrite /s {s}.
rewrite Habba.
apply: pure_typing_tidy_many_poly_abs_closed; first done.
rewrite Habba.
apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
rewrite Habba.
apply: pure_typing_many_poly_abs_contains_tidy_closed; [done | by eassumption |].
set ξ := (ξ in ren_poly_type ξ _).
rewrite tidy_ren_poly_type.
have ->: [poly_abba] = map (ren_poly_type ξ) [poly_abba] by done.
apply: pure_typing_ren_poly_type.
rewrite Habba.
apply: pure_typing_tidy_many_poly_abs_closed; first done.
rewrite /= tidy_many_poly_abs_le /=; first by lia.
rewrite tidy_many_poly_abs_le /=.
{
do ? (rewrite ?allfv_poly_type_many_poly_abs /=).
rewrite ?iter_scons ?iter_scons_ge; by lia.
}
rewrite tidy_many_poly_abs_le /=; first by lia.
rewrite tidy_many_poly_abs_le /=.
{
do ? (rewrite ?allfv_poly_type_many_poly_abs /=).
rewrite ?iter_scons ?iter_scons_ge; by lia.
}
rewrite tidy_many_poly_abs_le /=; first by lia.
rewrite tidy_many_poly_abs_le /=; first by lia.
apply: (pure_typing_pure_var 0); first done.
apply: contains_poly_abbaI; congr poly_var; by lia.
}
move=> /pure_typing_weaken_closed => /(_ []) H /pure_typing_tidyI /= /H{H} => /(_ ltac:(done)).
move=> /(pure_typing_ren_poly_type (Nat.pred)) /= /pure_typableI.
congr pure_typable.
congr cons.
rewrite ?map_map.
apply: map_ext => ?.
by rewrite ?tidy_ren_poly_type tidy_tidy ?poly_type_norm ren_poly_type_id /=.
