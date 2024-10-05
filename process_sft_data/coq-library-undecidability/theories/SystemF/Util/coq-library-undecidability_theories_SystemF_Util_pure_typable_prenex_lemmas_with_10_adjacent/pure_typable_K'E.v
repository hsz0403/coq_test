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

Lemma pure_typing_K'I {Gamma M N t}: pure_typing Gamma M t -> pure_typable Gamma N -> pure_typing Gamma (K' M N) t.
Proof.
move=> HM [tN HtN].
apply: (pure_typing_pure_app_simpleI (s := tN)); last done.
apply: pure_typing_pure_abs_simpleI.
Admitted.

Lemma pure_typing_K'E {Gamma M N t} : pure_typing Gamma (K' M N) t -> pure_typing Gamma M t /\ pure_typable Gamma N.
Proof.
rewrite /K'.
move=> /pure_typingE [n] [?] [?] [?] [+] [+] [H1C ->] => /pure_typingE'.
move=> /(pure_typing_ren_pure_term_allfv_pure_term Nat.pred (Delta := (map (ren_poly_type (Nat.add n)) Gamma))).
apply: unnest.
{
rewrite allfv_pure_term_ren_pure_term /=.
by apply: allfv_pure_term_TrueI.
}
rewrite renRen_pure_term ren_pure_term_id.
move=> /(pure_typing_contains H1C) /pure_typing_many_poly_absI HM.
move=> /(pure_typing_ren_poly_type (fun x => x - n)) /pure_typableI HN.
constructor; first done.
congr pure_typable: HN.
rewrite map_map.
apply: map_id' => ?.
Admitted.

Lemma pure_typable_K'I {Gamma M N}: pure_typable Gamma M -> pure_typable Gamma N -> pure_typable Gamma (K' M N).
Proof.
move=> [tM] ? ?.
exists tM.
Admitted.

Lemma leftmost_poly_var_ren_poly_type {ξ t} : leftmost_poly_var (ren_poly_type ξ t) = omap ξ (leftmost_poly_var t).
Proof.
elim: t ξ; [done | by move=> ? + ? _ ? /= => -> |].
move=> t + ? /= => ->.
Admitted.

Lemma leftmost_poly_var_subst_poly_type {σ t} : leftmost_poly_var (subst_poly_type σ t) = obind (σ >> leftmost_poly_var) (leftmost_poly_var t).
Proof.
elim: t σ; [done | by move=> ? + ? _ ? /= => -> |].
move=> t + σ /= => ->.
case: (leftmost_poly_var t); last done.
move=> [|x] /=; first done.
rewrite /funcomp /= leftmost_poly_var_ren_poly_type.
Admitted.

Lemma leftmost_poly_var_many_poly_abs {n t x} : leftmost_poly_var (many_poly_abs n t) = Some x <-> leftmost_poly_var t = Some (n+x).
Proof.
elim: n x; first done.
move=> n /= IH x.
have ->: S (n + x) = n + S x by lia.
rewrite -IH.
case: (leftmost_poly_var (many_poly_abs n t)); last done.
move=> [|y]; first done.
Admitted.

Lemma leftmost_path_length_ren_poly_type {ξ t} : leftmost_path_length (ren_poly_type ξ t) = leftmost_path_length t.
Proof.
elim: t ξ; [done | by move=> ? + ? _ ? /= => -> |].
move=> t + ? /= => ->.
Admitted.

Lemma leftmost_path_length_subst_poly_type {σ t} : leftmost_path_length (subst_poly_type σ t) = (if leftmost_poly_var t is Some x then leftmost_path_length (σ x) else 0) + leftmost_path_length t.
Proof.
elim: t σ; [done | by move=> ? + ? _ ? /= => -> |].
move=> t + σ /= => ->.
case: (leftmost_poly_var t); last done.
move=> [|x] /=; first done.
Admitted.

Lemma leftmost_path_length_many_poly_abs {n t} : leftmost_path_length (many_poly_abs n t) = leftmost_path_length t.
Proof.
Admitted.

Lemma contains_leftmost_path_length_eq {n s t} : contains (many_poly_abs n s) t -> not (is_poly_abs s) -> match leftmost_poly_var s with | None => leftmost_path_length s = leftmost_path_length t | Some x => n <= x -> leftmost_path_length s = leftmost_path_length t end.
Proof.
move Es': (many_poly_abs n s) => s' /clos_rt_rt1n_iff Hs't.
elim: Hs't n s Es'.
-
move=> > <- _.
rewrite ?leftmost_path_length_many_poly_abs.
by case: (leftmost_poly_var _).
-
move=> > [] r > _ IH [|n]; first by case=> /=.
move=> s [?].
subst.
evar (s'' : poly_type).
have := IH n s''.
rewrite subst_poly_type_many_poly_abs.
subst s'' => /(_ ltac:(done)).
move: s {IH} => [x | s {}t | /=]; last done.
+
move=> /= + _ ?.
have ->: x = n + (1 + (x - n - 1)) by lia.
rewrite ?iter_up_poly_type_poly_type ?leftmost_poly_var_ren_poly_type ?leftmost_path_length_ren_poly_type /=.
apply; by [|lia].
+
move=> /(_ ltac:(done)).
rewrite leftmost_poly_var_subst_poly_type /=.
move Eox: (leftmost_poly_var s) => ox.
case: ox Eox.
*
move=> x Hsx /= + _ ?.
rewrite leftmost_path_length_subst_poly_type Hsx.
have ->: x = n + (1 + (x - n - 1)) by lia.
rewrite ?iter_up_poly_type_poly_type ?leftmost_poly_var_ren_poly_type ?leftmost_path_length_ren_poly_type /=.
apply.
by lia.
*
move=> /= Hs <- _.
Admitted.

Lemma pure_typable_self_application {Gamma x n t} : not (is_poly_abs t) -> nth_error Gamma x = Some (many_poly_abs n t) -> pure_typable Gamma (pure_app (pure_var x) (pure_var x)) -> exists y, y < n /\ leftmost_poly_var t = Some y.
Proof.
move=> Ht Hx /pure_typableE [?] [?] [].
move=> /pure_typingE' [?] [].
rewrite Hx => [[<-]] H1C.
move=> /pure_typingE [n3] [?] [s'] [+] [].
rewrite nth_error_map Hx => [[?]] H2C ?.
subst.
move: Ht H1C H2C.
clear => Ht + /contains_ren_poly_type_addLR.
move=> /contains_leftmost_path_length_eq + /contains_leftmost_path_length_eq.
move=> /(_ Ht) + /(_ Ht).
case: (leftmost_poly_var t).
-
move=> y H1y H2y.
exists y.
constructor; last done.
suff: (not (n <= y)) by lia.
move=> /copy [/H1y + /H2y] => -> /=.
rewrite leftmost_path_length_many_poly_abs leftmost_path_length_ren_poly_type.
by lia.
-
move=> -> /=.
rewrite leftmost_path_length_many_poly_abs leftmost_path_length_ren_poly_type.
Admitted.

Lemma pure_typing_Mω {Gamma t} : pure_typing Gamma Mω t -> exists n1 n2 s' t' y, t = many_poly_abs n1 (poly_arr (many_poly_abs n2 s') t') /\ y < n2 /\ leftmost_poly_var s' = Some y.
Proof.
rewrite /Mω.
move=> /pure_typingE [n1] [s] [t'] [+ ->].
have := many_poly_absI s.
move=> [n] [s'] [->].
move=> + /pure_typableI /pure_typable_self_application.
move=> + H => /H /= => /(_ _ ltac:(done)) [y] [? ?].
Admitted.

Lemma leftmost_poly_var_contains_poly_arr {s x s' t'} : leftmost_poly_var s = Some x -> contains s (poly_arr s' t') -> exists n'' s'' t'', s = many_poly_abs n'' (poly_arr s'' t'').
Proof.
have [n'' [s'' [?]]] := many_poly_absI s.
subst.
case Es'': (s''); [ move=> _ | by move=> *; do 3 eexists | by move=> /=].
rewrite leftmost_poly_var_many_poly_abs /=.
move=> [?].
subst => /contains_tidyI.
rewrite tidy_many_poly_abs_le /=; first by lia.
Admitted.

Lemma pure_typable_K'E {Gamma M N} : pure_typable Gamma (K' M N) -> pure_typable Gamma M /\ pure_typable Gamma N.
Proof.
by move=> [?] /pure_typing_K'E [/pure_typableI].
