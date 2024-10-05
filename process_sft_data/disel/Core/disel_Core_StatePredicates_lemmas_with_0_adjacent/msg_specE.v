From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX DepMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section SoupPredicates.
Definition msg_in_soup (from to : nid) (criterion : nat -> seq nat -> bool) (d : soup) : Prop := (exists! i, exists t c, find i d = Some (Msg (TMsg t c) from to true)) /\ forall i t c, find i d = Some (Msg (TMsg t c) from to true) -> criterion t c.
Definition msg_spec from to tg cnt := msg_in_soup from to (fun x y => (x == tg) && (y == cnt)).
Definition no_msg_from (from : nid) (d : soup) : Prop := forall i to tms b, find i d = Some (Msg tms from to b) -> b = false.
Definition no_msg_to (to : nid) (d : soup) : Prop := forall i from tms b, find i d = Some (Msg tms from to b) -> b = false.
Definition no_msg_from_to from to (d : soup) := forall i tms b, find i d = Some (Msg tms from to b) -> b = false.
Definition no_msg_from_imp from to d : no_msg_from from d -> no_msg_from_to from to d.
Proof.
by move=>H i; move: (H i to).
End SoupPredicates.
Definition no_msg_from_to' from to (criterion : nat -> seq nat -> bool) (d : soup) := forall i t c, find i d = Some (Msg (TMsg t c) from to true) -> ~~criterion t c.

Lemma msg_specE s from to tg cnt : valid s -> no_msg_from_to from to s -> msg_spec from to tg cnt (post_msg s (Msg (TMsg tg cnt) from to true)).1.
Proof.
move=>V H; split=>/=; last first.
-
move=>i t c; rewrite findUnR ?valid_fresh?V//.
case: ifP; last by move=>_/H.
rewrite domPt inE/==>/eqP Z; subst i.
by rewrite findPt/=; case=>E Z; subst c t; rewrite !eqxx.
exists (fresh s); split=>[|z[t][c]].
-
exists tg, cnt; rewrite findUnR ?valid_fresh?V//.
by rewrite domPt inE eqxx/=findPt/=.
rewrite findUnR ?valid_fresh?V// domPt !inE/=.
by case: ifP=>[|_/H]//; move/eqP=>->.
