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

Theorem pure_typable_intro_poly_arr_0_0 M : { N | forall Gamma, pure_typable (map tidy ((poly_arr (poly_var 0) (poly_var 0)) :: (map (ren_poly_type S) Gamma))) M <-> pure_typable (map tidy Gamma) N }.
Proof.
exists (M_Wells_J M) => Gamma.
constructor.
-
pose tI := poly_arr (poly_var 0) (poly_var 0).
move=> HM.
rewrite /M_Wells_J.
pose t0 := poly_arr tI tI.
exists t0.
apply: (pure_typing_pure_app_simpleI (s := poly_abs t0)).
+
apply: pure_typing_pure_abs_simpleI.
apply: pure_typing_K'I.
*
apply: (pure_typing_pure_app_simpleI (s := t0)).
**
apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
**
apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
*
pose s0 := poly_arr (poly_abs (poly_var 0)) (poly_abs (poly_var 0)).
exists s0.
apply: (pure_typing_pure_app_simpleI (s := s0)).
**
apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
**
apply: pure_typing_pure_abs_simpleI.
apply: (pure_typing_pure_app_simpleI (s := (poly_abs (poly_var 0)))).
***
apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
***
apply: (pure_typing_pure_var 0); [done | by apply /rt_step /contains_step_subst].
+
rewrite /M_Wells.
apply: (pure_typing_pure_abs 1).
apply: pure_typing_K'I; first by apply: pure_typing_pure_var_simpleI.
apply: pure_typable_K'I.
*
exists tI.
apply: pure_typing_pure_abs_simpleI.
apply: pure_typing_pure_app_simpleI; first by apply: pure_typing_pure_var_simpleI.
apply: pure_typing_pure_app_simpleI; by apply: pure_typing_pure_var_simpleI.
*
move: HM.
rewrite /= ?map_map.
congr pure_typable.
congr cons.
apply: map_ext => ?.
by rewrite tidy_ren_poly_type.
-
rewrite /M_Wells_J.
move=> /pure_typableE [s] [?] [].
move=> /pure_typingE' /pure_typableI /pure_typable_K'E [].
have [ns [s' [? Hs]]] := many_poly_absI s.
subst s.
rename s' into s.
move=> /copy [H00] /pure_typable_self_application => /(_ _ _ ltac:(eassumption) ltac:(done)).
move=> [y [Hyns Hsy]] H.
rewrite /M_Wells.
move=> /pure_typingE [nM] [?] [?] [+ /many_poly_abs_eqE'].
case Es: (s); [by move=> + [] | | by subst s].
clear Hs => + [?] [? ?].
subst.
move=> /pure_typing_K'E [] /pure_typingE [?] [?] [?] [[?]] [H1c ?].
subst.
move=> /pure_typable_K'E [/pure_typableE] [?] /pure_typableE [?] [?] [].
move=> /pure_typingE' [?] [[?]] H2c.
subst.
move=> /pure_typingE [?] [?] [?] [?] [+] [_] [H3c ?].
subst.
move=> /pure_typingE' [?] [[?]] H4c HM.
subst.
move: (Hsy) => /= /leftmost_poly_var_contains_poly_arr => /(_ _ _ ltac:(eassumption)).
move=> [?] [?] [?] ?.
subst.
move: Hsy.
rewrite /= leftmost_poly_var_many_poly_abs /=.
move: H => /pure_typable_pure_app_0_Mω H /H{H} [? ?].
subst.
move: H2c => /contains_poly_arrE [?] [?] [+ ?].
subst.
rewrite subst_poly_type_many_poly_abs /= iter_up_poly_type_poly_type.
rewrite fold_right_length_ts ?iter_up_poly_type_poly_type /=.
move=> /many_poly_abs_eqE'' => /(_ ltac:(done)) [?] [? ?].
subst.
move: H4c.
rewrite ren_poly_type_many_poly_abs /=.
move=> /contains_poly_arrE [?] [?] [? ?].
subst.
move: (H3c) => /contains_tidyI.
rewrite tidy_many_poly_abs_le /=; first by lia.
move=> /contains_poly_varE [?] [?].
set t := (t in ren_poly_type _ t).
have [nt' [t' [?]]] := many_poly_absI t.
subst t.
subst.
case Et': (t'); [move=> _ | move=> _ | by subst t'; move=> /= ].
+
subst t'.
move: (H1c).
rewrite ren_poly_type_many_poly_abs /=.
move=> /contains_sub [?] [?] [?] [?] _.
subst.
move: H00.
rewrite many_poly_abs_many_poly_abs.
move=> /pure_typable_pure_app_0_0' [y' ?] _.
subst.
move: H3c => /contains_tidyI.
rewrite tidy_many_poly_abs_le /=; first by lia.
rewrite tidy_subst_poly_type tidy_ren_poly_type tidy_many_poly_abs_le /=; first by lia.
rewrite iter_up_ren_ge; first by lia.
rewrite fold_right_length_ts_ge /=; first by lia.
move=> /containsE [?].
have ? : y = y' by lia.
subst.
move: HM => [?] /pure_typing_tidyI /=.
rewrite tidy_many_poly_abs_le /=.
{
rewrite ?allfv_poly_type_many_poly_abs /= ?iter_scons_ge; by lia.
}
rewrite tidy_many_poly_abs_le /=; first by lia.
rewrite tidy_many_poly_abs_le /=; first by lia.
move=> /(pure_typing_ren_poly_type (fun x => x - (nM - 1))) /= /pure_typableI.
congr pure_typable.
congr cons.
*
congr poly_arr; congr poly_var; by lia.
*
rewrite ?map_map.
apply: map_ext => ?.
rewrite ?tidy_ren_poly_type tidy_tidy ?poly_type_norm /=.
apply: extRen_poly_type.
by lia.
+
rewrite ren_poly_type_many_poly_abs subst_poly_type_many_poly_abs /=.
rewrite (svalP tidy_many_poly_abs).
by move: (sval _) => [? ?] /many_poly_abs_eqE' /= [].
