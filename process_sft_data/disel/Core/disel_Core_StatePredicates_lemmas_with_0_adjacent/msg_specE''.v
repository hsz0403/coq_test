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

Lemma msg_specE'' s from from' to to' tg cnt tms : valid s -> from == from' = false -> msg_spec from to tg cnt s -> msg_spec from to tg cnt (post_msg s (Msg tms from' to' true)).1.
Proof.
move=>V N H; split=>//=; last first.
-
move=>i t c; rewrite findUnR ?valid_fresh?V//.
rewrite domPt inE/=; case:ifP; last by move=>_; move/(proj2 H).
move/eqP=>Z; subst i; rewrite findPt/=; case=>_ Z.
by subst from'; rewrite eqxx in N.
case: (H)=>H' _; case: H'=>i; case=>[[t]][c] U1 U2.
exists i; split=>//.
-
exists t, c; rewrite findUnR ?valid_fresh?V//.
rewrite domPt inE/=; case:ifP=>//.
move/eqP=>Z; subst i.
by move/find_some: U1=>E; move:(dom_fresh s); rewrite E.
move=>z[t'][c']; rewrite findUnR ?valid_fresh?V//.
rewrite domPt inE/=; case:ifP=>//; last first.
-
by move=>_ G; apply: (U2 z); exists t', c'.
move/eqP=>Z; subst z.
rewrite findPt/=; case=>Z1 Z2.
by subst from'; rewrite eqxx in N.
