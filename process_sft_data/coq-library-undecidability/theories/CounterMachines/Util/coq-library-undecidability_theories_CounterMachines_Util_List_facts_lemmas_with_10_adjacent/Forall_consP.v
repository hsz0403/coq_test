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

Lemma Forall_nilP : Forall P [] <-> True.
Proof.
Admitted.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof.
rewrite Forall_consP Forall_nilP.
Admitted.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
elim: A.
{
constructor; by [|case].
}
move=> ? ? IH /=.
rewrite ? Forall_consP ? IH.
Admitted.

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
elim: l.
{
move=> /=.
by constructor.
}
move=> a l IH /=.
Admitted.

Lemma Forall_concatP {X : Type} {P : X -> Prop} {ls : list (list X)} : Forall P (concat ls) <-> Forall (fun l => Forall P l) ls.
Proof.
elim: ls.
{
move=> /=.
by constructor.
}
move=> l ls IH /=.
Admitted.

Lemma Forall_flat_map_iff {T U: Type} {P : T -> Prop} {ds : list U} {f : U -> list T} : Forall P (flat_map f ds) <-> Forall (fun d => Forall P (f d)) ds.
Proof.
Admitted.

Lemma nth_error_map {X Y: Type} {f: X -> Y} {l: list X} {n: nat} : nth_error (map f l) n = omap f (nth_error l n).
Proof.
elim: n l; first by case.
move=> n IH.
case; first done.
move=> x l /=.
Admitted.

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
Admitted.

Lemma nth_repeat {X: Type} {x: X} {n m: nat}: nth n (repeat x m) x = x.
Proof.
Admitted.

Lemma Forall_consP {a A} : Forall P (a :: A) <-> P a /\ Forall P A.
Proof.
constructor.
{
move=> H.
by inversion H.
}
move=> [? ?].
by constructor.
