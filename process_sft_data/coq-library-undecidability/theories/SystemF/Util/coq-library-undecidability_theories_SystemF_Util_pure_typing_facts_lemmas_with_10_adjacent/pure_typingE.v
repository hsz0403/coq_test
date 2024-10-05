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

Lemma pure_typingE' {Gamma M t} : pure_typing Gamma M t -> match M with | pure_var x => match t with | poly_var _ | poly_arr _ _ => exists s, nth_error Gamma x = Some s /\ contains s t | poly_abs _ => True end | pure_app M N => match t with | poly_var _ | poly_arr _ _ => exists s t', pure_typing Gamma M (poly_arr s t') /\ pure_typing Gamma N s /\ contains t' t | poly_abs _ => True end | pure_abs M => match t with | poly_var _ => False | poly_arr s t => pure_typing (s :: Gamma) M t | poly_abs _ => True end end.
Proof.
case: M.
-
move=> > /pure_typingE [n] [?] [?] [+] [].
case: t; last done.
all: (case: n; [rewrite map_ren_poly_type_id /=; subst | done]).
all: (move=> *; subst; eexists; constructor; by eassumption).
-
move=> > /pure_typingE [n] [?] [?] [?] [+] [+] [].
case: t; last done.
all: (case: n; [rewrite map_ren_poly_type_id /=; subst | done]).
all: (move=> *; subst; (do 2 eexists); constructor; [| constructor]; by eassumption).
-
move=> > /pure_typingE [n] [?] [?] [].
case: t; last done.
all: (case: n; [rewrite map_ren_poly_type_id /=; subst | done]).
+
done.
+
Admitted.

Lemma contains_stepI {s t t'}: t' = subst_poly_type (s .: poly_var) t -> contains_step (poly_abs t) t'.
Proof.
move=> ->.
Admitted.

Lemma contains_ren_poly_typeI ξ {s t} : contains s t -> contains (ren_poly_type ξ s) (ren_poly_type ξ t).
Proof.
elim.
-
move=> > [] > /=.
apply: rt_step.
rewrite poly_type_norm /=.
have := contains_step_subst.
evar (s' : poly_type) => /(_ s').
evar (t' : poly_type) => /(_ t').
congr contains_step.
subst t'.
rewrite poly_type_norm /=.
apply: ext_poly_type.
subst s'.
by case.
-
move=> ?.
by apply: rt_refl.
-
move=> *.
Admitted.

Lemma contains_subst_poly_typeI σ {s t} : contains s t -> contains (subst_poly_type σ s) (subst_poly_type σ t).
Proof.
elim.
-
move=> > [] > /=.
apply: rt_step.
rewrite poly_type_norm /=.
have := contains_step_subst.
evar (s' : poly_type) => /(_ s').
evar (t' : poly_type) => /(_ t').
congr contains_step.
subst t'.
rewrite poly_type_norm /=.
apply: ext_poly_type.
subst s'.
case; first done.
move=> ?.
by rewrite /= poly_type_norm /= subst_poly_type_poly_var.
-
move=> ?.
by apply: rt_refl.
-
move=> *.
Admitted.

Lemma contains_ren_poly_type_addLR {n s t} : contains (ren_poly_type (Nat.add n) s) t -> contains s (ren_poly_type (fun x => x - n) t).
Proof.
move=> /(contains_ren_poly_typeI (fun x => x - n)).
congr contains.
Admitted.

Lemma containsE {t t'} : contains t t' -> match t with | poly_var _ => t = t' | poly_arr _ _ => t = t' | poly_abs t => (poly_abs t) = t' \/ exists s, contains (subst_poly_type (scons s poly_var) t) t' end.
Proof.
move=> /clos_rt_rt1n_iff.
case.
-
case: t; [done | done | by left].
-
move=> > [] > /clos_rt_rt1n_iff ?.
right.
eexists.
Admitted.

Lemma contains_sub {n s t t''} : contains (many_poly_abs n (poly_arr s t)) t'' -> exists n' s' t', t'' = many_poly_abs n' (poly_arr s' t') /\ contains (many_poly_abs n s) (many_poly_abs n' s') /\ contains (many_poly_abs n t) (many_poly_abs n' t').
Proof.
move Es1: (many_poly_abs n _) => s1 /clos_rt_rt1n_iff Hs1s2.
elim: Hs1s2 n s t Es1.
-
move=> > <-.
do 3 eexists.
constructor; first done.
constructor; by apply: rt_refl.
-
move=> > [] r > _ IH [|n] > /=; first done.
move=> [] /(congr1 (subst_poly_type (r .: poly_var))).
rewrite subst_poly_type_many_poly_abs /= => /IH [?] [?] [?] [->].
rewrite -?subst_poly_type_many_poly_abs => - [? ?].
do 3 eexists.
constructor; first done.
Admitted.

Lemma contains_sub' {n s t n' s' t'} : contains (many_poly_abs n (poly_arr s t)) (many_poly_abs n' (poly_arr s' t')) -> contains (many_poly_abs n s) (many_poly_abs n' s') /\ contains (many_poly_abs n t) (many_poly_abs n' t').
Proof.
Admitted.

Lemma typing_contains {s t Gamma P} : contains s t -> typing Gamma P s -> exists Q, erase P = erase Q /\ typing Gamma Q t.
Proof.
move=> /clos_rt_rt1n_iff => H.
elim: H P.
-
move=> ? ? ?.
by eexists.
-
move=> ? ? ? [] s' ? _ IH P.
Admitted.

Lemma pure_typing_pure_var_simpleI {Gamma x t} : nth_error Gamma x = Some t -> pure_typing Gamma (pure_var x) t.
Proof.
move=> Hx.
apply: (pure_typing_pure_var 0); last by apply: rt_refl.
rewrite nth_error_map Hx /=.
Admitted.

Lemma pure_typingE {Gamma M t} : pure_typing Gamma M t -> match M with | pure_var x => exists n s t', nth_error (map (ren_poly_type (Nat.add n)) Gamma) x = Some s /\ contains s t' /\ t = many_poly_abs n t' | pure_app M N => exists n s t' t'', pure_typing (map (ren_poly_type (Nat.add n)) Gamma) M (poly_arr s t') /\ pure_typing (map (ren_poly_type (Nat.add n)) Gamma) N s /\ contains t' t'' /\ t = many_poly_abs n t'' | pure_abs M => exists n s t', pure_typing (s :: map (ren_poly_type (Nat.add n)) Gamma) M t' /\ t = many_poly_abs n (poly_arr s t') end.
Proof.
case => *; [do 3 eexists | do 4 eexists | do 3 eexists]; by eauto.
