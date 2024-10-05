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

Lemma rely_consume_other l s s' m tm from: network_rely s s' -> find m (dsoup (gets s l)) = Some (Msg tm from this true) -> find m (dsoup (gets s' l)) = Some (Msg tm from this true).
Proof.
case=>n; elim: n s=>/=[?[-> C]|n Ih s [z][s''][N] S R E]//.
by rewrite -(@Ih s'' R)=>//; clear Ih; apply: (step_consume_other N S).
