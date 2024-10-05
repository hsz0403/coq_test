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

Lemma msg_spec_consumeE i d from to from' to' t c' t' cond: valid d -> find i d = Some (Msg (TMsg t' c') from' to' true) -> msg_in_soup' from to t cond d -> [|| (from != from'), (to != to') | (t != t')] -> msg_in_soup' from to t cond (consume_msg d i).
Proof.
move=>V E S N.
case: S=>[][j][[c]F]H1 H2.
have Nij: i != j.
-
case H: (i == j)=>//.
move/eqP in H; subst i; move: E; rewrite F=>[][???]; subst.
move: N=>/orP []/eqP; first by congruence.
move/eqP/orP; case; first by move=>X Z; subst to'; rewrite eqxx in X.
by rewrite eqxx.
split.
-
exists j; split; first by exists c; rewrite mark_other// eq_sym; apply/negbTE.
move=> x [c1][E'].
case H: (x == i).
+
by move/eqP in H; subst x; rewrite (find_consume _ E) in E'.
by apply: H1; exists c1; rewrite mark_other in E'.
move=>k c1.
case H: (k == i); first by move/eqP in H; subst k; rewrite (find_consume _ E).
by rewrite mark_other//; apply: H2.
