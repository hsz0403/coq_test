From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Rely.
Variable w : world.
Variable this: nid.
Notation getl := (getLocal).
Notation gets := getStatelet.
Notation getp := (@getProtocol _ w).
Fixpoint network_rely' n s1 s2 := if n is n'.+1 then exists z s3, [/\ this != z, network_step w z s1 s3 & network_rely' n' s3 s2] else s1 = s2 /\ s1 \In Coh w.
Definition network_rely s1 s2 := exists n, network_rely' n s1 s2.
Notation loc i l := (getLocal this (getStatelet i l)).
Notation msgs i l := (dsoup (getStatelet i l)).
End Rely.

Lemma step_send_other' l s s' m tm to b z: this != z -> network_step w z s s' -> find m (dsoup (gets s l)) = Some (Msg tm this to b) -> exists b', find m (dsoup (gets s' l)) = Some (Msg tm this to b') /\ (b' -> b).
Proof.
move=>N S.
case: (S)=>[[H1 <-->] | k st _ to' a loc' pf D C S' Ph Spf ->/= | k rt _ m' from' pf D C tm' T [H2 H3->/=]]//; do?[by exists b]; move: (coh_coh l C); rewrite /gets findU; case B: (l == k)=>//=; do?[by exists b]; move/eqP: B=>B; subst k; rewrite (stepV1 S).
-
case: (dom_find l s)=>[|d->_ C']; first by move/find_none; rewrite D.
rewrite joinC findPtUn2; last first.
+
rewrite joinC valid_fresh; apply: (cohVs C').
case B: (m == fresh (dsoup d)); last by move=>->; exists b.
move/eqP:B=>B; subst m; move: (dom_fresh (dsoup d))=>B.
by move/find_some=>E; rewrite E in B.
move: H2; move: (coh_s l C) pf; rewrite /gets; case B: (m == m'); do[move/eqP: B=>Z; subst m'|]; case: (dom_find l s)=>[|d->_ C' pf H2 _]; do?[by move=>->? ? _; rewrite/consume_msg !find0E].
-
rewrite /consume_msg; case B: (find m (dsoup d))=>[v|]; last by rewrite B.
rewrite /mark_msg findU eqxx/= (cohVs C')/==>E; rewrite B in H2; clear B.
case: v H2 E=>c x y a; case=>Z1 Z2 Z3 Z4; subst c x y a=>/=.
by case=>Z1 Z2 Z3 Z4; subst b to from' tm'; exists false.
rewrite/consume_msg; case B': (find m' (dsoup d))=>[v|]; last by exists b.
by rewrite findU B/==>->; exists b.
