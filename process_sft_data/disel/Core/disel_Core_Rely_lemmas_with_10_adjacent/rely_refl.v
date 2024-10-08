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

Lemma rely_trans s1 s2 s3 : network_rely s1 s2 -> network_rely s2 s3 -> network_rely s1 s3.
Proof.
case=>n; elim: n s1 s2=>[?? [<-]|n Hi s1 s2]//.
move=>[z][s4][N]H1 H2 H3; case: (Hi _ _ H2 H3)=>m H4.
Admitted.

Lemma rely_coh' n s1 s2 : network_rely' n s1 s2 -> Coh w s1 /\ Coh w s2.
Proof.
Admitted.

Lemma rely_coh s1 s2 : network_rely s1 s2 -> Coh w s1 /\ Coh w s2.
Proof.
Admitted.

Lemma rely_loc s1 s2 l: network_rely s1 s2 -> find this (dstate (gets s1 l)) = find this (dstate (gets s2 l)).
Proof.
case=>n; elim: n s1=>/=[s1 [E C]|n Ih s1 [z][s''][N]S R]; first by subst s2.
Admitted.

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
Admitted.

Lemma rely_consume_other l s s' m tm from: network_rely s s' -> find m (dsoup (gets s l)) = Some (Msg tm from this true) -> find m (dsoup (gets s' l)) = Some (Msg tm from this true).
Proof.
case=>n; elim: n s=>/=[?[-> C]|n Ih s [z][s''][N] S R E]//.
Admitted.

Lemma step_send_other l s s' m tm to b z: this != z -> network_step w z s s' -> find m (dsoup (gets s' l)) = Some (Msg tm this to b) -> exists b', find m (dsoup (gets s l)) = Some (Msg tm this to b') /\ (b -> b').
Proof.
move=>N S.
case: (S)=>[[H1 <-->] | k st _ to' a loc' pf D C S' Ph Spf ->/= | k rt _ m' from' pf D C tm' T [H2 H3->/=]]//; do?[by exists b]; move: (coh_coh l C); rewrite /gets findU; case B: (l == k)=>//=; do?[by exists b]; move/eqP: B=>B; subst k; rewrite (stepV1 S).
-
case: (dom_find l s)=>[|d->_ C']; first by move/find_none; rewrite D.
rewrite joinC findPtUn2; last first.
+
rewrite joinC valid_fresh; apply: (cohVs C').
case B: (m == fresh (dsoup d)); first by case=>_ Z _; subst; move/eqP: N.
by move=>H; exists b; split.
move: H2; move: (coh_s l C) pf; rewrite /gets; case B: (m == m'); do[move/eqP: B=>Z; subst m'|]; case: (dom_find l s)=>[|d->_ C' pf H2 _]; do?[by move=>->? ? _; rewrite/consume_msg !find0E].
-
rewrite /consume_msg; case B: (find m (dsoup d))=>[v|]; last by rewrite B.
rewrite /mark_msg findU eqxx/= (cohVs C')/==>E; rewrite B in H2; clear B.
case: v H2 E=>c x y a; case=>Z1 Z2 Z3 Z4; subst c x y a=>/=.
by case=>Z1 Z2 Z3 Z4; subst b to from' tm'; exists true; split.
rewrite/consume_msg; case B': (find m' (dsoup d))=>[v|]; last by exists b.
Admitted.

Lemma rely_send_other l s s' m tm to b: network_rely s s' -> find m (dsoup (gets s' l)) = Some (Msg tm this to b) -> exists b', find m (dsoup (gets s l)) = Some (Msg tm this to b') /\ (b -> b').
Proof.
case=>n; elim: n s=>/=[?[-> C]|n Ih s [z][s''][N] S R E]//; first by exists b.
case: (@Ih s'' R E)=>b''[H1 H2].
Admitted.

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
Admitted.

Lemma rely_send_other' l s s' m tm to b: network_rely s s' -> find m (dsoup (gets s l)) = Some (Msg tm this to b) -> exists b', find m (dsoup (gets s' l)) = Some (Msg tm this to b') /\ (b' -> b).
Proof.
case=>n; elim: n s b; first by move=>s b[Z C]; subst s'; exists b.
move=>n Ih s b [z][s''][N] S R H.
case: (step_send_other' N S H)=>c[H3 H4].
Admitted.

Lemma rely_refl s : s \In Coh w -> network_rely s s.
Proof.
move=>H; by exists 0.
