Require Import List.
Import ListNotations.
Require Import Arith Lia.
Require Import ssreflect ssrbool ssrfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Maximal Implicit Insertion.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Section ForallNorm.
Variable T : Type.
Variable P : T -> Prop.
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).
End ForallNorm.

Lemma Forall_concatP {X : Type} {P : X -> Prop} {ls : list (list X)} : Forall P (concat ls) <-> Forall (fun l => Forall P l) ls.
Proof.
elim: ls.
{
move=> /=.
by constructor.
}
move=> l ls IH /=.
by rewrite ? Forall_norm IH.
