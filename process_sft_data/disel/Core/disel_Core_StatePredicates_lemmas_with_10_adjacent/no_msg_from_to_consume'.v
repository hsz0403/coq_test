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

Lemma msg_specE_consume1 s pt from to to' tg cnt i m : valid s -> find i s = Some {| content := m; from := from; to := to'; active := true |} -> (pt != from) -> msg_spec pt to tg cnt s -> msg_spec pt to tg cnt (consume_msg s i).
Proof.
intros.
eapply msg_specE_consume; eauto.
Admitted.

Lemma msg_specE_consume2 s pt from to to' tg cnt i m : valid s -> find i s = Some {| content := m; from := from; to := to'; active := true |} -> (to != to') -> msg_spec pt to tg cnt s -> msg_spec pt to tg cnt (consume_msg s i).
Proof.
intros.
eapply msg_specE_consume; eauto.
Admitted.

Definition no_msg_from_imp from to d : no_msg_from from d -> no_msg_from_to from to d.
Proof.
Admitted.

Lemma no_msg_from_toE from to s tms to': valid s -> no_msg_from_to from to s -> to == to' = false -> no_msg_from_to from to (post_msg s (Msg tms from to' true)).1.
Proof.
move=>V H X/= i m b; rewrite findUnR ?valid_fresh?V//.
case: ifP; last by move=>_/H.
rewrite domPt inE/==>/eqP Z; subst i.
Admitted.

Lemma no_msg_from_toE' from to s tms from' to': valid s -> no_msg_from_to from to s -> from' == from = false -> no_msg_from_to from to (post_msg s (Msg tms from' to' true)).1.
Proof.
move=>V H X/= i m b; rewrite findUnR ?valid_fresh?V//.
case: ifP; last by move=>_/H.
rewrite domPt inE/==>/eqP Z; subst i.
Admitted.

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
Admitted.

Lemma msg_specE' s from to to' tg cnt tms : valid s -> to == to' = false -> msg_spec from to tg cnt s -> msg_spec from to tg cnt (post_msg s (Msg tms from to' true)).1.
Proof.
move=>V N H; split=>//=; last first.
-
move=>i t c; rewrite findUnR ?valid_fresh?V//.
rewrite domPt inE/=; case:ifP; last by move=>_; move/(proj2 H).
move/eqP=>Z; subst i; rewrite findPt/=; case=>_ Z.
by subst to'; rewrite eqxx in N.
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
Admitted.

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
Admitted.

Lemma has_all_true xs (ps : seq nid) x: perm_eq [seq i.1 | i <- xs] ps -> all id [seq i.2 | i <- xs] -> x \in ps -> (x, true) \in xs.
Proof.
move=>P A D; move: (perm_eq_mem P x).
rewrite D=>/mapP[z] I Z; subst x.
rewrite all_map/= in A; move/allP: A=>/(_ z I)/=<-.
Admitted.

Lemma has_some_false (xs : seq (nid * bool)) ps x: perm_eq [seq i.1 | i <- xs] ps -> x \in ps -> exists b, (x, b) \in xs.
Proof.
move=>P D; move: (perm_eq_mem P x).
rewrite D=>/mapP[z] I Z; subst x.
Admitted.

Lemma no_msg_from_to_consume' from to cond s i: valid s -> no_msg_from_to' from to cond s -> no_msg_from_to' from to cond (consume_msg s i).
Proof.
move=>V H m t c .
rewrite /consume_msg; case: (find i s); last by move=>F; apply: (H m t c F).
move=>ms; case B: (m == i).
-
by move/eqP: B=>B; subst m; rewrite findU eqxx/= V.
by rewrite findU B/==>/(H m t c).
