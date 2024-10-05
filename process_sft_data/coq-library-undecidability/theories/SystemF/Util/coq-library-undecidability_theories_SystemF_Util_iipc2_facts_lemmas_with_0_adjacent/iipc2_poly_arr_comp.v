Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Lemma iipc2_poly_arr_comp {Gamma s r t} : iipc2 Gamma (poly_arr s r) -> iipc2 Gamma (poly_arr r t) -> iipc2 Gamma (poly_arr s t).
Proof.
move=> [?] /(@typing_ren_term' S) HP1 [?] /(@typing_ren_term' S) HP2.
eexists.
apply: typing_abs.
apply: typing_app; first by apply: HP2.
apply: typing_app; first by apply: HP1.
by apply: (typing_var (x := 0)).
