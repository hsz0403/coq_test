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

Lemma pure_typing_trace_poly_typeE {s ns Gamma t n}: is_simple s -> allfv_poly_type (gt (length ns)) s -> pure_typing ((map (fun x => poly_var (n + x)) ns) ++ poly_abba :: Gamma) (trace_poly_type (length ns) s) t -> ren_poly_type (fun x => n + nth x ns 0) s = tidy t.
Proof.
elim: s Gamma t n.
-
move=> x Gamma t n _ /= ? /pure_typingE [n1] [?] [?].
rewrite ?nth_error_map nth_error_app1; first by rewrite map_length; lia.
rewrite nth_error_map.
have -> := nth_error_nth' ns 0; first by lia.
move: (nth x ns 0) => y [[?]] [].
subst.
move=> /containsE ? ->.
subst.
rewrite tidy_many_poly_abs_le /=; first by lia.
congr poly_var.
by lia.
-
move=> s1 IH1 s2 IH2 Gamma t n /= [/IH1 {}IH1 /IH2 {}IH2] [/IH1 {}IH1 /IH2 {}IH2].
move=> /pure_typingE [n1] [?] [?] [?] [+] [+] [H1C ?].
subst.
move=> /pure_typingE' [?] [?] [+] [+] H2C.
move=> /pure_typingE' [?] [+] H3C.
rewrite ?nth_error_map nth_error_app2; first by rewrite ?map_length; lia.
rewrite ?map_length (ltac:(lia) : length ns - length ns = 0) /=.
move=> [?].
subst.
move: H3C => /(contains_poly_arrE (n := 2)) => - [[|r1 [|r2 [|? ?]]]] [] //=.
move=> _ [? ?].
subst.
move: H2C => /containsE [? ?].
subst.
move: H1C => /containsE ?.
subst.
rewrite ?map_app /= ?map_map /=.
under [map _ ns]map_ext => x do rewrite (ltac:(lia) : n1 + (n + x) = (n1 + n) + x).
move=> /IH2 {}IH2 /IH1 {}IH1.
rewrite -tidy_many_poly_abs_tidy /= -IH1 -IH2.
rewrite tidy_many_poly_abs_le /=.
{
rewrite ?allfv_poly_type_ren_poly_type /=.
constructor; apply: allfv_poly_type_TrueI; by lia.
}
rewrite IH1 IH2 ?tidy_tidy -IH1 -IH2 ?poly_type_norm /=.
congr poly_arr; apply: extRen_poly_type; by lia.
-
done.
