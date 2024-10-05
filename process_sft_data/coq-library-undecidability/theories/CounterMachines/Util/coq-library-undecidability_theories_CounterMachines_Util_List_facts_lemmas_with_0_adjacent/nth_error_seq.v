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

Lemma nth_error_seq {m l n: nat} : n < l -> nth_error (seq m l) n = Some (m+n).
Proof.
elim: n m l.
{
move=> m [|l]; first by lia.
move=> /= _.
congr Some.
by lia.
}
move=> n IH m [|l /= ?]; first by lia.
rewrite /nth_error -/(nth_error _ _) IH; [|congr Some]; by lia.
