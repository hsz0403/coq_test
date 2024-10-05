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

Lemma msg_spec_consume s from to tg cnt cnt' i : valid s -> find i s = Some {| content := TMsg tg cnt'; from := from; to := to; active := true |} -> msg_spec from to tg cnt s -> no_msg_from_to from to (consume_msg s i).
Proof.
move=>V E[][j][[t][c]]F H1 H2.
move=>m tms b; rewrite /consume_msg; move: (find_some E).
case: dom_find=>// msg->_ _; case B: (m == i).
-
by move/eqP: B=>B; subst m; rewrite findU eqxx/= V; case.
have X: j = i by apply: (H1 i); exists tg, cnt'.
subst j; rewrite findU B/=; case: b=>// E'.
suff X: i = m by subst i; rewrite eqxx in B.
by apply: (H1 m); case: tms E'=>t' c' E'; exists t', c'.
