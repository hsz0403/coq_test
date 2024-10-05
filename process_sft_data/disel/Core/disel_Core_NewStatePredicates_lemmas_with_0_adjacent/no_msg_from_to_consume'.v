From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX DepMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section NewSoupPredicates.
Definition msg_in_soup' from to t (cond : seq nat -> bool) (d : soup) := (exists! i, exists c, find i d = Some (Msg (TMsg t c) from to true)) /\ forall i c, find i d = Some (Msg (TMsg t c) from to true) -> cond c.
Definition msg_spec' from to tg cnt := msg_in_soup' from to tg (fun y => (y == cnt)).
Definition no_msg_from_to' from to (criterion : nat -> seq nat -> bool) (d : soup) := forall i t c, find i d = Some (Msg (TMsg t c) from to true) -> ~~criterion t c.
End NewSoupPredicates.

Lemma no_msg_from_to_consume' from to cond s i: valid s -> no_msg_from_to' from to cond s -> no_msg_from_to' from to cond (consume_msg s i).
Proof.
move=>V H m t c .
rewrite /consume_msg; case: (find i s); last by move=>F; apply: (H m t c F).
move=>ms; case B: (m == i).
-
by move/eqP: B=>B; subst m; rewrite findU eqxx/= V.
by rewrite findU B/==>/(H m t c).
