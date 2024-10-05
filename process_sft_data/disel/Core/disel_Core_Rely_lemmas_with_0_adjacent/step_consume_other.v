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

Lemma step_consume_other l s s' m tm from z: this != z -> network_step w z s s' -> find m (dsoup (gets s l)) = Some (Msg tm from this true) -> find m (dsoup (gets s' l)) = Some (Msg tm from this true).
Proof.
move=>N S.
case: (S)=>[[H1 <-] | k st _ to a loc' pf D C S' Pf Spf ->/= | k rt _ m' from' pf D C tm' T [H2 H3->/=]]//; move: (coh_coh l C); rewrite /gets findU; case B: (l == k)=>//=; move/eqP: B=>B; subst k; rewrite (stepV1 S).
-
case: (dom_find l s)=>[|d->_]; first by move/find_none; rewrite D.
move=> C' E; rewrite -E; rewrite joinC findPtUn2; last first.
+
rewrite joinC valid_fresh; apply: (cohVs C').
case: ifP=>///eqP; move/find_some: E=>F Z.
by move/negbTE: (dom_fresh (dsoup d)); rewrite -Z F.
move: H2=>{H3}; move: (coh_s l C) pf; rewrite /gets.
case: (dom_find l s)=>[|d-> _ C' pf H2 _]; first by move/find_none; rewrite D.
case B: (m == m'); do[move/eqP: B=>Z; subst|move=>H].
-
by rewrite H2; case=>Z1 Z2 Z3; subst z; move/negbTE: N; rewrite eqxx.
rewrite /consume_msg; case B: (find m' (dsoup d))=>[v|]//= H.
by rewrite findU; move/eqP/negbTE: Z=>->/=.
