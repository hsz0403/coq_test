Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Lemma iipc2_generalization {Gamma Gamma' t} : Forall (iipc2 Gamma') Gamma -> iipc2 Gamma t -> iipc2 Gamma' t.
Proof.
move=> H [P HP].
elim: P Gamma Gamma' t HP H.
-
move=> > /typingE /nth_error_In.
rewrite Forall_forall.
by move=> + H => /H.
-
move=> ? IH1 ? IH2 > /typingE [?] [/IH1{}IH1 /IH2{}IH2].
move=> /copy [/IH1 [? ?] /IH2 [? ?]].
eexists.
apply: typing_app; by eassumption.
-
move=> s > IH Gamma Gamma' > /typingE [?] [->] /IH.
move=> /(_ (s :: Gamma')) + HG.
apply: unnest.
{
constructor.
-
exists (var 0).
by apply: typing_var.
-
move: HG.
apply: Forall_impl.
move=> ?.
apply: iipc2_weakening => ? /=.
clear.
by firstorder done.
}
move=> [? ?].
eexists.
apply: typing_abs.
by eassumption.
-
move=> ? IH > /typingE [?] [->] /IH{}IH /IH [? ?].
eexists.
apply: typing_ty_app.
by eassumption.
-
move=> > IH Gamma Gamma' > /typingE [?] [->] /IH.
move=> /(_ (map (ren_poly_type S) Gamma')) + HG.
apply: unnest.
{
rewrite Forall_mapP.
apply: Forall_impl HG.
move=> ? [Q].
eexists.
apply: typing_ren_poly_type.
by eassumption.
}
move=> [? ?].
eexists.
apply: typing_ty_abs.
by eassumption.
