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
constructor; (apply: rt_trans; [| by eassumption]); by apply /rt_step.
