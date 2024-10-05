Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Lemma iipc2_poly_arrE {Gamma s t}: iipc2 Gamma (poly_arr s t) -> iipc2 (s :: Gamma) t.
Proof.
move=> [?] /(@typing_ren_term' S) => /(_ (s :: Gamma) ltac:(done)).
move=> /typing_app => /(_ (var 0)) H.
eexists.
apply: H.
by apply: typing_var.
