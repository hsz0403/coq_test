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

Lemma msg_specE_consume s pt from to to' tg cnt i m : valid s -> find i s = Some {| content := m; from := from; to := to'; active := true |} -> (pt != from) || (to != to') -> msg_spec pt to tg cnt s -> msg_spec pt to tg cnt (consume_msg s i).
Proof.
move=>V E N[][j][[t][c]]F H1 H2.
have Nij: i != j.
-
case H: (i == j)=>//.
move/eqP in H.
subst i.
move: E.
rewrite F.
case.
intros.
subst.
move: N=>/orP[]/eqP; congruence.
split.
-
exists j.
split.
+
exists t, c.
rewrite mark_other// eq_sym.
by apply /negbTE.
+
move => x [t'][c'].
case H: (x == i).
*
move /eqP in H.
subst x.
by rewrite (find_consume _ E)//.
*
rewrite mark_other//.
eauto.
-
move=>k t' c'.
case H: (k == i).
+
move /eqP in H.
subst.
rewrite (find_consume _ E) //.
+
rewrite mark_other//.
eauto.
