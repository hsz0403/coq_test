Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
Require Import Undecidability.SystemF.Util.Facts Undecidability.SystemF.Util.poly_type_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Fixpoint allfv_pure_term (p: nat -> Prop) (M: pure_term) := match M with | pure_var x => p x | pure_app M N => allfv_pure_term p M /\ allfv_pure_term p N | pure_abs M => allfv_pure_term (scons True p) M end.
Fixpoint pure_var_bound (M: pure_term) := match M with | pure_var x => 1 + x | pure_app M N => 1 + pure_var_bound M + pure_var_bound N | pure_abs M => 1 + pure_var_bound M end.

Lemma allfv_pure_term_ren_pure_term {p ξ M} : allfv_pure_term p (ren_pure_term ξ M) <-> allfv_pure_term (ξ >> p) M.
Proof.
elim: M ξ p.
-
done.
-
move=> ? IH1 ? IH2 > /=.
by rewrite IH1 IH2.
-
move=> ? IH > /=.
rewrite IH.
constructor; apply: allfv_pure_term_impl; by case.
