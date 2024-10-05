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

Lemma last_key_mono f1 f2 : {subset dom f1 <= dom f2} -> last_key f1 <= last_key f2.
Proof.
rewrite leq_eqVlt orbC=>H; apply: (@keys_last_mono _ _ _ f1 f2); try by apply: hist_path.
by move=>x /=; move: (H x).
