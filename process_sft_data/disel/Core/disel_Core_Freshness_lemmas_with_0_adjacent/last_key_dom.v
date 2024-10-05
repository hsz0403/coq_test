From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Keys.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).
End Keys.
Section FreshLastKey.
Variable V : Type.
Implicit Type f : union_map [ordType of nat] V.
Definition last_key f := last 0 (dom f).
Definition fresh f := (last_key f).+1.
End FreshLastKey.

Lemma last_key_dom f : valid f -> last_key f \notin dom f -> f = Unit.
Proof.
rewrite /valid /= /last_key /Unit /= !umEX /= -{4}[f]UMC.tfE.
case: (UMC.from f)=>//=; case=>s H /= H1 _ /seq_last_in.
rewrite /UM.empty UMC.eqE UM.umapE /supp fmapE /= {H H1}.
by elim: s.
