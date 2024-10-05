Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
Require Import Undecidability.SystemF.Util.Facts Undecidability.SystemF.Util.poly_type_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Fixpoint allfv_pure_term (p: nat -> Prop) (M: pure_term) := match M with | pure_var x => p x | pure_app M N => allfv_pure_term p M /\ allfv_pure_term p N | pure_abs M => allfv_pure_term (scons True p) M end.
Fixpoint pure_var_bound (M: pure_term) := match M with | pure_var x => 1 + x | pure_app M N => 1 + pure_var_bound M + pure_var_bound N | pure_abs M => 1 + pure_var_bound M end.

Lemma ren_pure_term_id {M} : ren_pure_term id M = M.
Proof.
elim: M.
-
done.
-
move=> /=.
congruence.
-
move=> /=.
rewrite /upRen_pure_term_pure_term.
move=> > ?.
under extRen_pure_term => ? do rewrite up_ren_id.
by congruence.
