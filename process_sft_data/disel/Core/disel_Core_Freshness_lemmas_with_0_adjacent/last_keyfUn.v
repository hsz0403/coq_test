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

Lemma last_keyfUn f1 f2 : valid (f1 \+ f2) -> last_key f1 <= last_key (f1 \+ f2).
Proof.
by move=>X; apply: last_key_mono=>x; rewrite domUn inE X => ->.
