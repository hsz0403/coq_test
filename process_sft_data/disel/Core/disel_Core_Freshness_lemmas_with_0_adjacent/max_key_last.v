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

Lemma max_key_last f x : x \in dom f -> {in dom f, forall y, y <= x} -> last_key f = x.
Proof.
rewrite /last_key !umEX; case: (UMC.from f)=>//; case=>s H _ /=.
move=>H1 /= H2; apply: sorted_max_key_last (sorted_oleq H) H1 _.
by move=>z /(H2 z); rewrite leq_eqVlt orbC.
