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

Lemma valid_fresh' f v i w : valid (f \+ i \\-> w) -> valid (f \+ fresh (f \+ i \\-> w) \\-> v).
Proof.
move=> W; rewrite joinC validPtUn.
move: (dom_fresh (f \+ i \\-> w)); rewrite domUn inE; rewrite W/=.
by rewrite negb_or=>/andP; case=>-> _;move/validL: W=>->.
