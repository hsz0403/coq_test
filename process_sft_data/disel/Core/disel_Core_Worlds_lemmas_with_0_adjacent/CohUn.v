From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module WorldGetters.
Section WorldGetters.
Definition context := union_map Label protocol.
Definition hook_domain := [ordType of ((nat * Label) * (Label * nat))%type].
Definition hook_type := heap -> heap -> seq nat -> nid -> Prop.
Definition hooks := union_map hook_domain hook_type.
Definition world := (context * hooks)%type.
Definition getc (w: world) : context := fst w.
Coercion getc : world >-> context.
Definition geth (w: world) : hooks := snd w.
Coercion geth : world >-> hooks.
Variable w : world.
Variables (p : protocol).
Definition getProtocol i : protocol:= match find i (getc w) with | Some p => p | None => EmptyProt i end.
End WorldGetters.
End WorldGetters.
Export WorldGetters.
Module Worlds.
Module Core.
Section Core.
Definition hooks_consistent (c : context) (h : hooks) : Prop := forall z lc ls t, ((z, lc), (ls, t)) \in dom h -> (lc \in dom c) && (ls \in dom c).
Definition hook_complete w := hooks_consistent (getc w) (geth w).
Definition Coh (w : world) : Pred state := fun s => let: c := fst w in let: h := snd w in [/\ valid w, valid s, hook_complete w, dom c =i dom s & forall l, coh (getProtocol w l) (getStatelet s l)].
Section MakeWorld.
Variable p : protocol.
Notation l := (plab p).
Definition mkWorld : world := (l \\-> p, Unit).
End MakeWorld.
End Core.
End Core.
End Worlds.
Export Worlds.Core.

Lemma CohUn (w1 w2 : world) (s1 s2 : state) : Coh w1 s1 -> Coh w2 s2 -> valid (w1 \+ w2) -> Coh (w1 \+ w2) (s1 \+ s2).
Proof.
case: w1=>[c1 h1]; case: w2=>[c2 h2]; move=>C1 C2 V.
case: (C1)=>_ G1 K1 J1 H1; case: (C2)=>_ G2 K2 J2 H2.
case/andP: V=>V V'; simpl in V, V'.
have X: valid (s1 \+ s2).
-
case: validUn=>//; [by rewrite G1|by rewrite G2|move=>l; rewrite -J1 -J2=>D1 D2].
by case: validUn V=>//=V1 V2; move/(_ _ D1); rewrite D2.
have Y: dom (c1 \+ c2) =i dom (s1 \+ s2).
-
by move=>z; rewrite !domUn !inE/=;rewrite V X/= J1 J2.
have Z1: valid ((c1, h1) \+ (c2, h2)) by rewrite /valid/= V V'.
split=>//[|l]; last first.
-
rewrite /getProtocol /getStatelet.
case: (dom_find l (s1 \+ s2))=>[|v]Z.
-
by move/find_none: (Z); rewrite -Y; case: dom_find=>//->_; rewrite Z.
move/find_some: (Z)=>D; rewrite Z; rewrite -Y in D=> E.
case: dom_find D=>// p Z' _ _; rewrite Z'.
rewrite findUnL // in Z; rewrite findUnL // J1 in Z'.
by case: ifP Z Z'=>_ F1 F2; [move: (H1 l)|move: (H2 l)]; rewrite /getProtocol /getStatelet F1 F2.
by move=>z lc ls t/=; rewrite domUn inE=>/andP[_]/orP[];[move/K1|move/K2]; move/andP=>[A1 A2]; rewrite !domUn !inE A1 A2 V -?(orbC true).
