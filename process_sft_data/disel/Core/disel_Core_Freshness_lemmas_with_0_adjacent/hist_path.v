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

Lemma hist_path f : path oleq 0 (dom f).
Proof.
rewrite !umEX; case: (UMC.from f)=>// {f} f /= _; case: f; case=>//= x s H.
rewrite {1}/oleq /ord /= orbC -leq_eqVlt /=.
by apply: sub_path H=>z y; rewrite /oleq=>->.
