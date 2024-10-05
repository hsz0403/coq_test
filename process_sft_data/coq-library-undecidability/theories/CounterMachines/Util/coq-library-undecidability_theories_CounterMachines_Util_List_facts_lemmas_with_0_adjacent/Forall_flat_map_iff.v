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

Lemma Forall_flat_map_iff {T U: Type} {P : T -> Prop} {ds : list U} {f : U -> list T} : Forall P (flat_map f ds) <-> Forall (fun d => Forall P (f d)) ds.
Proof.
by rewrite flat_map_concat_map Forall_concatP Forall_mapP.
