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

Lemma no_msg_from_consume from from' to s i m : find i s = Some {| content := m; from := from'; to := to; active := true |} -> valid s -> no_msg_from from s -> no_msg_from from (consume_msg s i).
Proof.
move=>F V NM j to' tms b.
case H: (j == i).
-
move /eqP in H.
subst j.
rewrite (find_consume _ F) //.
by case.
rewrite mark_other//.
exact: NM.
